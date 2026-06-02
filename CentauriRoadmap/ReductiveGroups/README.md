# Roadmap: reductive algebraic groups (paved)

Background: Kevin Buzzard on Zulip —
[#mathlib4 > Definition of group scheme?](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Definition.20of.20group.20scheme.3F)
and [#Is there code for X? > Algebraic groups](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Algebraic.20groups).

This roadmap is to be **paved**: wherever there is a genuine modelling choice — Hopf
algebras vs. group objects in schemes vs. functor-of-points — we build **all** the
models and **all** the equivalences between them, rather than committing to one. As
Kevin and Adam Topaz put it, "the case of groups is sufficiently important that we
should have various approaches ... and provide explicit equivalences between the
various cats."

## The models

1. **Group objects in schemes.** A linear algebraic group over a field `k` is an
   affine group scheme of finite type:
   ```lean
   variable (k : Type*) [Field k]
   variable (G : Scheme) (φ : G ⟶ Spec(k))
     [GrpObj (Over.mk φ)] [IsAffine G] [LocallyOfFiniteType φ]
   ```
2. **Commutative Hopf algebras.** Over a base ring `R`, an affine group scheme is a
   commutative Hopf algebra `A` — `HopfAlgebra R A`. (Good for the finite/flat case,
   e.g. Oort–Tate, Raynaud; calculations happen in the Hopf algebra.)
3. **Functor of points** (Yoneda / Lawvere-theory flavour). Joël Riou's `Internal`
   approach: a contravariant functor to groups that is representable after forgetting
   the group structure. Worth carrying as a third model where it simplifies
   constructions.

**Pave it:** build all three and the equivalences, so a downstream proof can work in
whichever model is most convenient and transport results across.

## First concrete targets (Kevin's two bridges)

The back-and-forth between affine group schemes over a general ring base and Hopf
algebras. The Toric project already has these (and the round trip); we consume them
once the pin includes [mathlib4#39281](https://github.com/leanprover-community/mathlib4/pull/39281).

```lean
open CategoryTheory AlgebraicGeometry CommRingCat Scheme Opposite Spec
open scoped SpecOfNotation
variable (R : Type u) [CommRing R]

-- Γ(G) is an R-Hopf algebra, for G an affine group scheme over Spec R:
example (G : Scheme) (φ : G ⟶ Spec(R)) [GrpObj (Over.mk φ)] [IsAffine G] :
    HopfAlgebra R (Γ.obj (op G)) := sorry

-- the affine group scheme Spec A over Spec R associated to a Hopf algebra A:
example (A : Type u) [CommRing A] [HopfAlgebra R A] :
    GrpObj (Over.mk (map (ofHom (algebraMap R A)) : Spec(A) ⟶ Spec(R))) := sorry
```

(The compiled forms, when they elaborate against the pin, live in `Targets.lean`.)

## What to pave on top

- **Affine group scheme of finite type over a field → linear algebraic group**; basic
  API (kernels, images, the component group, `LocallyOfFiniteType`).
- **Connectedness** of a group scheme; the identity component `G°`.
- **Reductive.** Needs the (co)representation theory of the group — the unipotent
  radical and its triviality — so develop representations of `G` (equivalently
  comodules over the Hopf algebra) in tandem; this is *why* the bare Hopf-algebra view
  is not enough on its own.
- Worked admissible **examples**: `𝔾ₐ`, `𝔾ₘ`, `GLₙ`, `SLₙ`, tori, and crucially
  `μ_p` (not connected in char 0, not reduced in char p) — the definition must admit
  these, so we do **not** bake in `reduced`/`connected`.

> **No monolithic `LinearAlgebraicGroup` / `Variety`.** Following Kevin: these mean
> different things to different people; spell out exactly the hypotheses each result
> needs instead of committing to one umbrella definition.

## Prerequisites

`GrpObj` for schemes, `HopfAlgebra`, and the Hopf-algebra ↔ affine-group-scheme
equivalence from Toric (#39281). Promote the sketches above into compiled `Targets.lean`
declarations as the pin advances to include them.
