#!/usr/bin/env python3
"""Queue housekeeping: close PRs that have used up their review budget, and close duplicate roadmap PRs.

The TauCetiReview engine already auto-merges green PRs (review.yml `enable_automerge`). This covers the
other two janitorial jobs, now in CI so the autonomous worker can stay focused on producing work:

  abandon  Close any open PR the review engine has labelled `review-budget-spent`: it used its full
           review budget without reaching an all-green review. The engine clears the label if a later
           round fixes the PR. The branch is kept, and the closing comment says it is fine to open a
           fresh PR after another look at the approach.
  dedup    Close a newer PR that authors the same roadmap target (the `<!--tauceti-target:v1 ...-->`
           body marker) as an older open one. Keep the lowest PR number.

The one override is a `keep` label (also `hold`/`wip`/`human`/`do-not-close`): a PR with one of those
is never auto-closed. abandon is a server-side label query, so it costs one request no matter how many
PRs are open (the engine does the per-PR budget bookkeeping as it reviews); it then leaves alone any
labelled PR whose head commit landed after the label was applied, since a fix is in flight and the
re-review has not cleared the label yet. A failed close makes the job exit nonzero.

Env: GH_TOKEN (a token that can close PRs), REPO (owner/name), optional DRY_RUN=1, BUDGET_LABEL.
"""
import json
import os
import re
import subprocess
import sys

REPO = os.environ["REPO"]
DRY_RUN = os.environ.get("DRY_RUN") == "1"
# The label the TauCetiReview engine applies when a PR has spent its review budget without going green.
BUDGET_LABEL = os.environ.get("BUDGET_LABEL", "review-budget-spent")

TARGET_MARKER_RE = re.compile(r"<!--tauceti-target:v1 \{[^}]*\}-->")
TARGET_ID_RE = re.compile(r'"id"\s*:\s*"([^"]+)"')
KEEP_LABELS = {"keep", "hold", "wip", "human", "do-not-close"}
ABANDON_COMMENT = (
    "Closing automatically: this PR used its review budget without reaching an all-green review, so the "
    "queue housekeeping is retiring it to keep things moving. The branch is kept, so nothing is lost. It "
    "is completely fine to open a fresh PR once you have had another think about the approach. Add the "
    "`keep` label if you would rather it stay open.")
DEDUP_COMMENT = (
    "Closing automatically: this PR authors the same roadmap target (`{tid}`) as the older open #{kept}. "
    "The queue housekeeping keeps the earlier PR and closes this duplicate to avoid redundant review. "
    "The branch is kept; add the `keep` label if it is intentionally distinct.")


def gh_json(args):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args)} failed: {r.stderr.strip()}")
    return json.loads(r.stdout or "null")


def has_keep_label(pr: dict) -> bool:
    return bool({(l.get("name") or "").lower() for l in (pr.get("labels") or [])} & KEEP_LABELS)


def pushed_after_label(pr: int, head: str) -> bool:
    """True if the PR's head commit landed after the budget label was last applied — a fix is in
    flight and the re-review has not cleared the label yet, so we must not close. Fails safe (returns
    True) on any uncertainty, so a transient API error never causes a wrong close. O(labelled PRs)."""
    try:
        timeline = gh_json(["api", "--paginate", f"/repos/{REPO}/issues/{pr}/timeline?per_page=100"])
        added = [e.get("created_at") for e in (timeline or [])
                 if e.get("event") == "labeled" and (e.get("label") or {}).get("name") == BUDGET_LABEL]
        if not added:
            return True                                  # labelled but no event found: don't risk it
        commit = gh_json(["api", f"/repos/{REPO}/commits/{head}"])
        head_time = ((commit or {}).get("commit") or {}).get("committer", {}).get("date", "")
        if not head_time:
            return True
        return head_time > max(added)
    except RuntimeError as e:
        print(f"abandon: #{pr} freshness check failed ({e}); leaving it", file=sys.stderr)
        return True


def close(pr: int, comment: str) -> bool:
    """Close the PR with a comment. Returns True on success (or in dry-run), False on failure."""
    if DRY_RUN:
        print(f"[dry-run] would close #{pr}: {comment[:60]}...")
        return True
    r = subprocess.run(["gh", "pr", "close", str(pr), "--repo", REPO, "--comment", comment],
                       capture_output=True, text=True)
    if r.returncode == 0:
        print(f"closed #{pr}")
        return True
    print(f"close of #{pr} failed: {r.stderr.strip()}", file=sys.stderr)
    return False


def main() -> int:
    failures = 0
    suffix = " [dry-run]" if DRY_RUN else ""

    # abandon: the engine has already decided these are spent and labelled them. Just close them
    # (unless a human asked to keep one). One query, independent of total open-PR count.
    spent = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--label", BUDGET_LABEL,
                     "--limit", "1000", "--json", "number,headRefOid,labels"]) or []
    print(f"abandon: {len(spent)} PR(s) labelled {BUDGET_LABEL}{suffix}")
    for p in spent:
        if has_keep_label(p):
            print(f"abandon: #{p['number']} is {BUDGET_LABEL} but has a keep label; leaving it")
            continue
        if pushed_after_label(p["number"], p.get("headRefOid", "")):
            print(f"abandon: #{p['number']} has a newer commit than its {BUDGET_LABEL} label "
                  "(a fix is in flight); leaving it")
            continue
        print(f"abandon: #{p['number']} ({BUDGET_LABEL})")
        failures += not close(p["number"], ABANDON_COMMENT)

    # dedup: a newer PR sharing a tauceti-target id with an older open one (keep the lowest number).
    # List-only (the marker is in the body), so this pages cheaply; the marker is on roadmap PRs only.
    limit = 2000
    prs = gh_json(["pr", "list", "--repo", REPO, "--state", "open", "--limit", str(limit),
                   "--json", "number,isDraft,body,labels"]) or []
    if len(prs) >= limit:
        print(f"warning: hit the {limit}-PR list limit; some open PRs may not be de-duplicated",
              file=sys.stderr)
    prs = [p for p in prs if not p.get("isDraft")]
    print(f"dedup: scanning {len(prs)} open PR(s){suffix}")
    seen: dict = {}
    for p in sorted(prs, key=lambda x: x["number"]):
        body = (p.get("body") or "").replace("\n", " ")
        mk = TARGET_MARKER_RE.search(body)
        if not mk:
            continue
        mid = TARGET_ID_RE.search(mk.group(0))
        if not mid:
            continue
        tid = mid.group(1)
        if tid not in seen:
            seen[tid] = p["number"]
            continue
        if has_keep_label(p):
            print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}') but has a keep "
                  "label; leaving it")
            continue
        print(f"dedup: #{p['number']} duplicates #{seen[tid]} (target '{tid}')")
        failures += not close(p["number"], DEDUP_COMMENT.format(tid=tid, kept=seen[tid]))

    if failures:
        print(f"housekeeping: {failures} close(s) failed", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as e:
        print(f"housekeeping: {e}", file=sys.stderr)
        sys.exit(1)
