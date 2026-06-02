# Roadmap: universal covers

**The whole universal-cover stack is absent from Mathlib, and we are not waiting for
it.** The construction sits in PRs that have stalled or died upstream:

- [mathlib4#31576](https://github.com/leanprover-community/mathlib4/pull/31576)
  (*quotient of paths by homotopy has the discrete topology*) — **closed, unmerged**.
- [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
  (*universal cover construction*) — open, depends on the closed #31576.
- [mathlib4#40135](https://github.com/leanprover-community/mathlib4/pull/40135)
  (*Deck transformation group*) — open.

So this roadmap is not "consume Mathlib once it catches up". It is: **port that
material into `Centauri/`, sorry-free and attributed, and build the rest of the theory
on top of it here.** Original roadmap content: the gist
<https://gist.github.com/kim-em/70e1762ab143b88605c699059769111c>.

Suggested home: `Centauri/AlgebraicTopology/UniversalCover/`. The one piece we *can*
consume from upstream is the general lifting criterion (see Stage 3).

## Stage 0 — port the foundations into `Centauri/`

Bring the existing, human-written construction into this library. It must land
sorry-free; each file should credit the original authors and the source PR.

1. **Discrete-fibre topology** (from #31576). For `X` semilocally simply connected and
   locally path-connected, the quotient of based paths by homotopy, fibred over
   endpoints, carries the discrete topology. This is the analytic heart the rest rests
   on; it died upstream, so it lives here.
2. **The based-path space and the cover** (from #38292):
   - `BasedPath x₀` and the path-component machinery of `endpoint ⁻¹' U`;
   - `UniversalCover x₀` as `BasedPath x₀` modulo endpoint-preserving homotopy, with the
     quotient topology, plus `proj` and the sheet decomposition;
   - `IsCoveringMap proj`, `PathConnectedSpace`, `SimplyConnectedSpace (UniversalCover x₀)`,
     and the universal lifting property `existsUnique_continuousMap_lifts`.
3. **The π₁ action** (from #38292, `Action.lean`): the action of `π₁(X, x₀)` on
   `UniversalCover x₀`, with `FaithfulSMul`, `ContinuousConstSMul`, the local-disjointness
   predicate, packaged as `UniversalCover.isQuotientCoveringMap`.
4. **Deck transformation group** (from #40135): `Deck p` as a `Subgroup (E ≃ₜ E)` for
   `p : E → X`, with the upstream `MulAction (X ≃ₜ X) X` / `FaithfulSMul` /
   `ContinuousConstSMul` instances; subgroup transfer gives `Deck p` its `Group`,
   `MulAction E`, `FaithfulSMul E`, `ContinuousConstSMul E`.

## Stage 1 — close out the universal cover

5. **`Deck(proj) ≃* π₁(X, x₀)`.** The bridge between Stage 0.3 and 0.4. Once it lands,
   `UniversalCover x₀ / π₁(X, x₀) ≃ X` follows. This is the natural first new theorem.

## Stage 2 — lifting criterion and Galois correspondence

6. **General lifting criterion.** This one *is* already in Mathlib —
   `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`
   (`Mathlib/Topology/Homotopy/Lifting.lean`), hypothesis `f_*(π₁ Y) ⊆ p_*(π₁ X̃)`,
   proved with no reference to a universal cover. **Consume it from upstream** — the
   exception that proves the rule.
7. **Cover associated to `H ≤ π₁(X, x₀)`.** `UniversalCover x₀ / H` is a connected cover
   with `p_*(π₁(–)) = H`; with (6) this is the existence half of the correspondence.
8. **Galois correspondence.** Bijection between conjugacy classes of subgroups of
   `π₁(X)` and isomorphism classes of pointed connected covers; normal subgroups ↔
   regular covers.

## Stage 3 — higher homotopy (a larger effort)

9.  **`p_* : π_n(X̃) ≅ π_n(X)` for `n ≥ 2`**, any cover. Needs general homotopy lifting
    (`I^n × I → X` lifts). Mathlib's `IsCoveringMap` has path lifting but not cube
    lifting — so we build cube lifting here too. Then the proof mirrors the `π₁`
    injectivity one-liner with `S^n` for `S^1`.
10. **Higher homotopy-group API.** Mathlib has `Ω^N X x` but a thin `HomotopyGroup`.
    Functoriality, basepoint-change iso, and `π_n(Y) = 0` for `n`-connected `Y` are
    prerequisites — built here.

## Stage 4 — applications

11. `π_n(S¹) = 0` for `n ≥ 2` (universal cover `ℝ` is contractible).
12. `π₁(S¹) ≅ ℤ` via deck transformations (Mathlib has this by another route — reconcile).
13. `π_n(Tᵏ)`, `π₁(RPⁿ)`, `K(G, 1)` spaces.

## Ordering

Stage 0 first — it is mostly a careful port, and unblocks everything. Then Stage 1 (5),
then Stage 2 (7)/(8). Stage 3 is a much bigger commitment (building homotopy-lifting and
higher-homotopy infrastructure, not just consuming it) and is best treated as a separate
track. As each milestone's prerequisite *types* exist in `Centauri/`, state the milestone
in `Targets.lean` (with `sorry`) and hand it to the AIs to discharge.
