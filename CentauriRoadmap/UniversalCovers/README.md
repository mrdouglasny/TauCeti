# Roadmap: universal covers

Follow-up work after [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
(`feat(AlgebraicTopology): universal cover construction`). Source roadmap:
the gist <https://gist.github.com/kim-em/70e1762ab143b88605c699059769111c>.

**Status (2026-06-02):**
- **Tier 1.1** — Deck transformations: in flight at
  [mathlib4#40135](https://github.com/leanprover-community/mathlib4/pull/40135).
- **Tier 1.2** — π₁ action on the universal cover (free + properly discontinuous):
  added to [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
  as `UniversalCover/Action.lean`, with `UniversalCover.isQuotientCoveringMap`.
- **Tier 2.4** — General lifting criterion: **already in mathlib** as
  `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`
  (`Mathlib/Topology/Homotopy/Lifting.lean:439`).

#38292 already gives, for `X` locally path-connected, path-connected, and
semilocally simply connected: `UniversalCover x₀` as a quotient of `BasedPath x₀`;
`proj : UniversalCover x₀ → X` with `IsCoveringMap`;
`SimplyConnectedSpace (UniversalCover x₀)`; and the universal lifting property via
`IsCoveringMap.existsUnique_continuousMap_lifts`.

Still missing from mathlib in this area: the Galois correspondence for covers,
general (cubical) homotopy lifting for covers, and substantial higher-homotopy-group
API.

> **Dependency note.** Most targets below depend on Mathlib PRs that are not yet
> merged (`#38292`, `#40135`). Until the pin (`lake-manifest.json`) advances to a
> commit containing them, the Lean statements live here as sketches rather than
> compiled `Targets.lean` declarations.

## Tier 1 — close out the universal cover

1. **Deck transformations as a group.** (In flight, `#40135`.) `Deck p` as a
   `Subgroup (E ≃ₜ E)` for arbitrary `p : E → X`, plus `MulAction (X ≃ₜ X) X`,
   `FaithfulSMul`, `ContinuousConstSMul`. Subgroup transfer gives `Deck p` its
   `Group`, `MulAction E`, `FaithfulSMul E`, `ContinuousConstSMul E`.
2. **The action of `π₁(X, x₀)` on `UniversalCover x₀`.** (Landed in `#38292`,
   `UniversalCover/Action.lean`.) Includes `FaithfulSMul`, `ContinuousConstSMul`,
   the local-disjointness predicate, packaged as `UniversalCover.isQuotientCoveringMap`.
3. **`Deck(proj) ≃* π₁(X, x₀)`.** *Outstanding — the natural next target*; bridges
   the two PRs above. Once landed, `UniversalCover x₀ / π₁(X, x₀) ≃ X` follows.

   ```lean
   -- once #38292 and #40135 are in the pin:
   noncomputable def deckEquivFundamentalGroup (x₀ : X) :
       Deck (UniversalCover.proj x₀) ≃* FundamentalGroup X x₀ := sorry
   ```

## Tier 2 — lifting criterion and Galois correspondence

4. **General lifting criterion.** Already in mathlib as
   `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` (`Lifting.lean:439`);
   hypothesis is `f_*(π₁ Y) ⊆ p_*(π₁ X̃)`. Proved without reference to a universal cover.
5. **Cover associated to `H ≤ π₁(X, x₀)`.** The quotient `UniversalCover x₀ / H` is a
   connected cover with `p_*(π₁(–)) = H`. With (4), this is the existence half of the
   Galois correspondence.
6. **Galois correspondence.** Bijection between conjugacy classes of subgroups of
   `π₁(X)` and isomorphism classes of pointed connected covers; normal subgroups ↔
   regular covers.

## Tier 3 — higher homotopy (a larger, separate effort)

7. **`p_* : π_n(X̃) ≅ π_n(X)` for `n ≥ 2`**, any cover. Needs general homotopy lifting
   (`I^n × I → X` lifts); mathlib's `IsCoveringMap` currently has path lifting but cube
   lifting must be added. Then the proof mirrors the `π₁` injectivity one-liner with
   `S^n` for `S^1`.
8. **Higher homotopy group API.** Mathlib has `Ω^N X x` but `HomotopyGroup` is thin.
   Functoriality, basepoint-change iso, and `π_n(Y) = 0` for `n`-connected `Y` are
   likely prerequisites.

## Tier 4 — applications

9.  `π_n(S¹) = 0` for `n ≥ 2` (universal cover `ℝ` is contractible).
10. `π₁(S¹) ≅ ℤ` via deck transformations (mathlib has this by another route — reconcile).
11. `π_n(Tᵏ)`, `π₁(RPⁿ)`, `K(G, 1)` spaces.

## Suggested ordering

Tier 1 is in flight; once both Tier 1 PRs land, **Tier 1.3** (`Deck ≃* π₁`) is the
natural next step, then Tier 2 (5)/(6) — mostly bookkeeping once (1)–(3) exist.
Tier 3 is a much bigger commitment (developing mathlib's higher-homotopy
infrastructure, not just consuming it) and should be treated as a separate effort.
