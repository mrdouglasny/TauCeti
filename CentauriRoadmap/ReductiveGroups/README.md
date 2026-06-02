# Roadmap: reductive algebraic groups (paved)

The theory of reductive algebraic groups is the long game: it underpins the Langlands
programme, automorphic forms, and much of FLT, and it is almost entirely absent from
Mathlib. **We are not waiting for it to appear upstream — we build it here**, in
`Centauri/`, as a large, iteratively-expandable tower. Suggested home:
`Centauri/Algebra/AlgebraicGroup/` (foundations) and `Centauri/AlgebraicGeometry/`
(the scheme-side dictionary).

This roadmap continues the experiment in
[mathlib4#34897](https://github.com/leanprover-community/mathlib4/pull/34897)
("experiment: Claude defining reductive groups") and its `PLAN.md`. That PR is an
honest sketch with **known bugs** — read it for both the design and the pitfalls
(the relevant ones are flagged inline below).

## Standing hypotheses

Spell hypotheses out; **do not** bundle them into one mega-class (Kevin Buzzard,
repeatedly on Zulip: separate typeclass assumptions let every result be proved in its
correct generality). Work over a field `k` to start; generalize to a base later. An
**affine algebraic group** over `k` is a smooth affine group scheme of finite type —
equivalently a commutative Hopf `k`-algebra `A` that is finitely generated and
*geometrically reduced* (smoothness). There will be **no** monolithic
`LinearAlgebraicGroup`/`Variety` definition — like Mathlib, we state exactly the
hypotheses each result needs, and we deliberately admit non-smooth/non-reduced examples
such as `μ_p` (so smoothness is a named hypothesis, never baked in).

## What "paved" means here

Maintain **three equivalent views** of an affine algebraic group and the explicit
equivalences between them, so any proof can work in whichever is most convenient:

1. **Commutative Hopf algebras** over `k` (the coordinate ring `A`).
2. **Group objects in schemes** — `GrpObj (Over.mk (φ : G ⟶ Spec k))` with `IsAffine`.
3. **The functor of points** — a representable group-valued functor `R ↦ Homₖ(A, R)`.

Representations are then **comodules over `A`**, and we keep the
representation ⇆ comodule ⇆ Tannakian dictionary in sync throughout. Wherever there is
a modelling fork (Hopf-ideal kernel vs. scheme-theoretic kernel; root data vs. dynamic
parabolics; reductive-via-unipotent-radical vs. linearly-reductive), **do both and
prove them equivalent** rather than committing.

## Inventory: what Mathlib master already gives us (consume)

- **Hopf/coalgebra algebra:** `Mathlib/RingTheory/HopfAlgebra/{Basic,GroupLike,TensorProduct}.lean`,
  `Mathlib/RingTheory/Coalgebra/{Convolution,GroupLike}.lean`.
- **Categorical group objects:** `Mathlib/CategoryTheory/Monoidal/{Mon_,Comon_,Bimon_,Grp_,CommGrp_}.lean`
  and the cartesian/`Over` variants — so view 2 is expressible (and Kevin's bridge
  statements below already elaborate).
- **Algebra categories:** `Mathlib/Algebra/Category/CoalgCat/ComonEquivalence.lean`
  (coalgebras ≃ comonoids), `Mathlib/Algebra/Category/CommAlgCat/{Basic,FiniteType,Monoidal}.lean`.
- **Scheme-side group theory:** `Mathlib/AlgebraicGeometry/Group/Abelian.lean` (the
  rigidity theorem: proper group schemes are commutative) and `…/Group/Smooth.lean`.
- **Smoothness ingredient:** `Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean`.
- **Combinatorial backbone for classification:** `Mathlib/LinearAlgebra/RootSystem/*`
  (root systems, bases, Cartan matrices) and `Mathlib/GroupTheory/Coxeter/*` (Weyl groups).
- **Representation theory (finite-group flavour, to generalize):**
  `Mathlib/RepresentationTheory/{FDRep,Character,Tannaka,Maschke,Semisimple,Irreducible}.lean`.

## Inventory: what is missing (build here)

Comodules over a coalgebra (**none in Mathlib**); the convolution group structure on the
functor of points; the explicit Hopf ⇆ affine-group-scheme equivalence (the Toric work,
[mathlib4#39281](https://github.com/leanprover-community/mathlib4/pull/39281), is not in
master); Hopf ideals / closed subgroup schemes and quotients; the identity component and
component group; Jordan decomposition; diagonalizable groups and tori with character
lattices; unipotent groups and the unipotent radical; reductive/semisimple groups; Borel
and parabolic subgroups, root data of a group, Bruhat/BN-pairs; and the classification.

---

## The build, in layers

Each layer is self-contained mathematics the next layer needs. As a layer makes the
next layer's *types* expressible, state that layer's milestones in `Targets.lean` (with
`sorry`) and hand them to the AIs to discharge in `Centauri/`.

### Layer 0 — the functor of points and the three-way dictionary
- **R-points as a group.** Generalize `AlgPoints R A := A →ₐ[k] R` for every `k`-algebra
  `R`; give it a group structure by **convolution** (not composition): multiplication
  `(f * g)(a) = ∑ f(a₁) g(a₂)`, identity the counit `ε`, inverse `f ∘ S`.
  - ⚠ Pitfall (#34897): `GroupLike k A` is **not** the points functor — for `GLₙ` the
    points are non-commutative, but group-like elements always form a commutative group.
  - Prerequisite lemma: the antipode is an anti-homomorphism, `S(ab) = S(b) S(a)`
    (currently a TODO in `HopfAlgebra/Basic.lean`); then algebra homs are closed under
    convolution and `f ∘ S` is the inverse. Then prove functoriality in `R`.
- **The bridges (first concrete targets — already compile as `sorry` in `Targets.lean`):**
  ```lean
  -- Γ(G) is an R-Hopf algebra, for G an affine group scheme over Spec R:
  example (G : Scheme) (φ : G ⟶ Spec(R)) [GrpObj (Over.mk φ)] [IsAffine G] :
      HopfAlgebra R (Γ.obj (op G)) := sorry
  -- the affine group scheme Spec A over Spec R associated to a Hopf algebra A:
  example (A : Type u) [CommRing A] [HopfAlgebra R A] :
      GrpObj (Over.mk (map (ofHom (algebraMap R A)) : Spec(A) ⟶ Spec(R))) := sorry
  ```
  Build these into a full **anti-equivalence** `CommHopfAlg k ≌ AffGrpSch k`, and a third
  equivalence with representable group functors. (Consume `CoalgCat/ComonEquivalence`,
  `Grp_`, `CommAlgCat`; the Toric route gives one direction once available.)
- **Base change.** `K ⊗[k] A` as a Hopf algebra over `K` (use
  `HopfAlgebra/TensorProduct.lean`; #34897 leaves this `sorry`). Geometric notions are all
  defined after base change to `k̄`.

### Layer 1 — representations = comodules
- **Comodules** over a coalgebra/Hopf algebra `A`: a coaction `ρ : V → V ⊗ A` with
  coassociativity and counit; comodule morphisms; the (rigid monoidal) category of
  **finite-dimensional** comodules; tensor products, duals, the regular representation.
- **The dictionary:** representation of `G` ⇆ `A`-comodule; matrix coefficients.
- **Faithfulness done right:** a f.d. representation is faithful iff its **matrix
  coefficients generate `A`** — *not* iff the coaction is injective (⚠ #34897).
- **Embedding theorem (hard):** every affine group scheme of finite type has a faithful
  f.d. representation, i.e. a closed immersion `G ↪ GLₙ`.
- **Tannakian reconstruction:** recover `G` from its tensor category of representations
  (extend `RepresentationTheory/Tannaka.lean` from finite groups to this setting).

### Layer 2 — subgroups, quotients, components
- **Hopf ideals ↔ closed subgroup schemes:** an ideal `I` with `Δ(I) ⊆ I⊗A + A⊗I`,
  `ε(I)=0`, `S(I) ⊆ I`; the quotient Hopf algebra `A/I`; the anti-equivalence; kernels.
- **Normality and quotients:** normal = Hopf ideal stable under the adjoint coaction
  (needs the conjugation/adjoint morphism at Hopf level); quotient groups `G/H` by
  faithfully-flat descent; short exact sequences.
- **Identity component `G°` and component group `π₀(G)`:** geometric connectedness
  (`A ⊗ k̄` has no nontrivial idempotents — *stronger* than over `k`); the
  connected–étale sequence. (⚠ #34897's `IsConnected` should be the geometric notion.)

### Layer 3 — Jordan decomposition, diagonalizable groups, tori
- **Jordan decomposition** of elements into semisimple and unipotent parts (geometric,
  over `k̄`), functorial under representations.
- **Diagonalizable groups ↔ finitely generated abelian groups** (Cartier duality);
  `μ_n`, `𝔾_m`; the non-smooth example `μ_p` in characteristic `p`.
- **Tori:** split and non-split; the **character lattice** `X*(T)` and **cocharacter
  lattice** `X_*(T)` with their perfect pairing — the input to root data.

### Layer 4 — solvable and unipotent groups; the unipotent radical
- **Unipotent groups** (correct, geometric definition): `g ∈ G(k̄)` is unipotent iff
  `ρ_g − id` is nilpotent for **every** f.d. representation; equivalently `G` embeds in
  the upper-triangular unipotent `Uₙ`; equivalently `G` has no nontrivial characters.
  - ⚠ #34897's `IsUnipotent` is *vacuous* (it tests nilpotence in the reduced ring `A`,
    so only `g = 1` qualifies) — the correct definition needs comodule theory (Layer 1).
- **Lie–Kolchin**; solvable groups.
- **The unipotent radical `R_u(G)`** (the hard core, SGA3/Borel level): the maximal
  connected normal unipotent closed subgroup, as a Hopf ideal, defined geometrically as
  `R_u(G_{k̄})` descended to `k`. Existence needs a Noetherian/dimension argument or the
  `GLₙ` embedding.

### Layer 5 — reductive and semisimple groups
- **Reductive:** smooth, connected, with `R_u(G_{k̄})` trivial. **Semisimple:** radical
  `R(G)` trivial. Develop the radical, centre, and derived group.
- **Alternative paving — linearly reductive:** every f.d. representation is completely
  reducible. Equivalent to reductive in characteristic 0 (Maschke-flavoured; consume
  `Semisimple`/`Maschke`); *not* in characteristic `p`. Provide both definitions and the
  char-0 equivalence theorem, so downstream work can pick either.

### Layer 6 — structure theory
- **Borel subgroups, maximal tori**, and their conjugacy; **parabolic** subgroups and
  **Levi** decomposition.
- **Root datum** `(X*(T), Φ, X_*(T), Φ^∨)` of `(G, T)` with its **Weyl group** — consume
  `LinearAlgebra/RootSystem/*` and `GroupTheory/Coxeter/*`.
- **Bruhat decomposition** and **BN-pairs / Tits systems**. Keep the **dynamic** approach
  to parabolics/Levi/unipotent radical (Kevin, Shurui Liu, Stepan Nesterov on Zulip) as a
  parallel route that avoids full root data — useful for the `p`-adic representation-theory
  consumers, who can ask only for a BN-pair.

### Layer 7 — classification and existence (long horizon)
- The **isomorphism** and **existence theorems**: split reductive groups ↔ root data;
  classification of semisimple groups by Dynkin diagrams; isogenies; Chevalley existence.
- **Relative theory over a base** and **pseudo-reductive groups**
  (Conrad–Gabber–Prasad) — flagged as far-future generalizations.

---

## Worked examples (build alongside, as "checks along the way")

Concrete Hopf algebras / group schemes that exercise and validate the definitions:
`𝔾_a`, `𝔾_m`, `μ_n`/`μ_p`, `GLₙ`, `SLₙ`, `PGLₙ`, `SOₙ`, `Sp₂ₙ`, and tori. Prove they are
reductive where applicable by exhibiting root data **and** by complete reducibility, and
exercise Cartier duality. (Kevin's caution: don't *develop the general theory* from
`GLₙ` — but examples are exactly how we keep the definitions honest.)

## Design notes (from Zulip and #34897)

- **Functor of points is the notion of points** — not `GroupLike`, not just `k`-points.
- **Faithful = matrix coefficients generate `A`**, not "coaction injective".
- **Geometric notions** (connected, unipotent, reductive) are defined after base change
  to `k̄`.
- **Don't bundle** typeclasses; **admit** non-smooth/non-reduced groups (`μ_p`) and make
  smoothness an explicit hypothesis where used.
- **Pave**: keep the Hopf / group-object / functor-of-points views and the
  representation ⇆ comodule dictionary synchronized via explicit equivalences.

## Downstream consumers (why this matters)

`p`-adic representation theory of `G(K)` (smooth/admissible representations, Hecke
algebras — Shurui Liu et al.), the Langlands programme, automorphic forms (Kevin
Buzzard), and FLT. Several of these can start against a **BN-pair** or the dynamic
parabolic API before the full root-data classification exists — another reason to pave.

## References

- J. S. Milne, *Algebraic Groups* (2017) — the modern scheme-theoretic reference.
- W. C. Waterhouse, *Introduction to Affine Group Schemes* — Hopf algebras, comodules,
  closed subgroups, the unipotent radical.
- A. Borel, *Linear Algebraic Groups*; T. A. Springer, *Linear Algebraic Groups*.
- J. C. Jantzen, *Representations of Algebraic Groups*.
- B. Conrad, *Reductive Group Schemes* (SGA3 exposition); **SGA3**, Exposé XIX.
- B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups* (relative theory).
- Prior art: [mathlib4#34897](https://github.com/leanprover-community/mathlib4/pull/34897)
  and its `PLAN.md`.
