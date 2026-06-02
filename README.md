# Centauri

An *AIs-welcome* Lean 4 library downstream of [Mathlib](https://github.com/leanprover-community/mathlib4).

The name is a centaur: human-plus-AI. Humans hold the reins — roadmaps, CI, and
review — while AIs supply the horsepower, writing and reviewing the mathematics.
It is also the nearest star: the reachable frontier just downstream of Mathlib.

## Governance: who owns what

The directory layout *is* the governance boundary.

| Path | Owner | Contents |
| --- | --- | --- |
| `Centauri/` | **AIs** | All the Lean mathematics. **No `sorry`.** |
| `CentauriRoadmap/` | **humans** | Roadmaps (`README.md`) and target signatures (`Targets.lean`, where `sorry` is allowed — these are goals, not proofs). |
| `CentauriReview/` | **humans** | Review rubrics and (eventually) review bots. |
| `.github/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | **humans** | The rules of the game and the machinery that enforces them. |

This split has teeth, not just prose:

- **CODEOWNERS** (`.github/CODEOWNERS`) makes every path human-reviewed by default;
  AI author accounts only ever gain code-owner standing over `Centauri/`.
- **Branch protection** on `main` requires a passing CI run and code-owner review,
  and forbids direct pushes and force-pushes.
- **CI** (`.github/workflows/ci.yml`) builds against pinned Mathlib and enforces two
  invariants on `Centauri/`: it contains no `sorry`/`admit`/`sorryAx`, and it does
  not `import` the roadmap/review trees (so it cannot inherit sorried goals). The
  two `lean_lib` targets are a build convenience; this import guard is the real
  trust boundary.

### Rights matrix

- **AI accounts** may author PR branches touching **only `Centauri/`**. They may not
  edit CI/CODEOWNERS, administer the repo, push to `main`, or approve human-path PRs.
  AI peer-approval is allowed on `Centauri/` PRs once `ai-authors` is populated.
- **Humans** approve all human-governed PRs, own the roadmap and review machinery,
  and retain admin and merge rights.

## Mathlib dependency, and our stance toward it

Pinned to Mathlib **master** (`lakefile.toml` requires `rev = "master"`; the exact
commit is recorded in `lake-manifest.json`). Human stewards re-pin to known-good
commits over time. `lean-toolchain` tracks the pinned Mathlib's toolchain.

**We do not wait on Mathlib.** Upstreaming is slow and uncertain — PRs sit open for
months or close unmerged — so Centauri treats Mathlib as a stable foundation to build
*on*, not a queue to block *behind*. If a prerequisite we need is not in Mathlib, we
build it **here** and keep going. When a roadmap target depends on material that lives
only in an open or closed Mathlib PR, the rule is: copy that material into `Centauri/`
(sorry-free, attributed), and continue on top of it. If it later lands upstream, a
steward can delete our copy and re-pin — but nothing in this library is ever paused
waiting for that to happen.

## Building

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Roadmaps

The initial targets live under `CentauriRoadmap/`:

1. [Universal covers](CentauriRoadmap/UniversalCovers/README.md)
2. [The Jacobian challenge](CentauriRoadmap/JacobianChallenge/README.md) (Christian Merten's AG version)
3. [Reductive algebraic groups](CentauriRoadmap/ReductiveGroups/README.md) (paved: Hopf algebras *and* group objects)
