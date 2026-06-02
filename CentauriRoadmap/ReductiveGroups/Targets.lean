import Mathlib

/-!
# Reductive algebraic groups — target signatures

The narrative roadmap, the three models, and what to pave are in `README.md`.

This file attempts the two "bridge" targets between affine group schemes and Hopf
algebras (Kevin Buzzard). They are stated with `sorry` (allowed in this human-owned
roadmap library). If they fail to elaborate against the pinned Mathlib commit — e.g.
the `GrpObj` / `SpecOfNotation` API is not yet present — they are demoted to sketches
in `README.md` until the pin advances.
-/

open CategoryTheory AlgebraicGeometry CommRingCat Scheme Opposite Spec
open scoped SpecOfNotation

namespace CentauriRoadmap.ReductiveGroups

universe u

variable (R : Type u) [CommRing R]

/-- `Γ(G)` is an `R`-Hopf algebra, for `G` an affine group scheme over `Spec R`. -/
example (G : Scheme) (φ : G ⟶ Spec(R)) [GrpObj (Over.mk φ)] [IsAffine G] :
    HopfAlgebra R (Γ.obj (op G)) := sorry

/-- The affine group scheme `Spec A` over `Spec R` associated to a Hopf algebra `A`. -/
example (A : Type u) [CommRing A] [HopfAlgebra R A] :
    GrpObj (Over.mk (map (ofHom (algebraMap R A)) : Spec(A) ⟶ Spec(R))) := sorry

end CentauriRoadmap.ReductiveGroups
