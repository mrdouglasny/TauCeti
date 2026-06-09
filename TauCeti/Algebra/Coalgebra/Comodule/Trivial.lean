/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.Basic
import TauCeti.Algebra.Coalgebra.Comodule

/-!
# The trivial comodule over a bialgebra

For a bialgebra `C` over `R`, every `R`-module `M` has a trivial right `C`-comodule
structure with coaction `m ↦ m ⊗ 1`. This is the comodule-theoretic analogue of the trivial
representation. It is also the tensor unit ingredient for the monoidal category of comodules
over a Hopf algebra.

The main definition is intentionally an explicit named instance, not a global instance:
many modules carry nontrivial coactions, and typeclass search should not silently choose the
trivial one.

## Main definitions

* `TauCeti.Comodule.trivial`: the trivial right comodule on an `R`-module.
* `TauCeti.Comodule.Hom.ofTrivial`: any linear map is a comodule morphism between trivial
  comodules.
* `TauCeti.Comodule.Hom.trivialEquiv`: comodule morphisms between trivial comodules are
  equivalent to ordinary linear maps.

## References

This supplies a small prerequisite for the Tau Ceti reductive-groups roadmap,
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra", specifically the tensor-unit side of the requested tensor-product and rigid
monoidal comodule category. It uses Mathlib's bialgebra API from
`Mathlib.RingTheory.Bialgebra.Basic`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- The trivial right-comodule coaction `m ↦ m ⊗ 1`. -/
def trivialCoact : M →ₗ[R] M ⊗[R] C :=
  (TensorProduct.mk R M C).flip 1

/-- The trivial right `C`-comodule structure on an `R`-module.

This is not registered as a global instance: an `R`-module can carry many coactions, and the
trivial one should be selected explicitly with `Comodule.trivial`. -/
@[reducible]
def trivial : Comodule R C M where
  coact := trivialCoact (R := R) (C := C) (M := M)
  coassoc := by
    ext m
    simp [trivialCoact, Algebra.TensorProduct.one_def]
  lTensor_counit_comp_coact := by
    ext m
    simp [trivialCoact]

section Trivial

attribute [local instance] trivial

/-- The coaction of the trivial right comodule sends `m` to `m ⊗ 1`. -/
@[simp]
theorem trivial_coact_apply (m : M) :
    coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  rfl

/-- The coaction of the trivial right comodule is the map `m ↦ m ⊗ 1`. -/
@[simp]
theorem trivial_coact :
    coact (R := R) (C := C) (M := M) = trivialCoact (R := R) (C := C) (M := M) :=
  rfl

/-- A linear map between trivial comodules is automatically a comodule morphism. -/
def Hom.ofTrivial (f : M →ₗ[R] N) : Hom R C M N where
  toLinearMap := f
  map_coact := by
    ext m
    simp [trivialCoact]

namespace Hom

/-- The underlying linear map of `Hom.ofTrivial f` is `f`. -/
@[simp]
theorem ofTrivial_toLinearMap (f : M →ₗ[R] N) :
    (ofTrivial (R := R) (C := C) f).toLinearMap = f :=
  rfl

/-- The comodule morphism induced by a linear map between trivial comodules applies as that
linear map. -/
@[simp]
theorem ofTrivial_apply (f : M →ₗ[R] N) (m : M) :
    ofTrivial (R := R) (C := C) f m = f m :=
  rfl

/-- The comodule morphism induced by the identity linear map between trivial comodules is
the identity comodule morphism. -/
@[simp]
theorem ofTrivial_id :
    ofTrivial (R := R) (C := C) (M := M) LinearMap.id = id R C M :=
  rfl

/-- The comodule morphism induced by a composite linear map between trivial comodules is the
composite of the induced comodule morphisms. -/
@[simp]
theorem ofTrivial_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    ofTrivial (R := R) (C := C) (g.comp f) =
      comp (ofTrivial (R := R) (C := C) g) (ofTrivial (R := R) (C := C) f) :=
  rfl

/-- Comodule morphisms between trivial comodules are exactly ordinary linear maps. -/
def trivialEquiv : Hom R C M N ≃ (M →ₗ[R] N) where
  toFun f := f.toLinearMap
  invFun f := ofTrivial (R := R) (C := C) f
  left_inv f := by
    ext m
    rfl
  right_inv f := rfl

/-- Applying `trivialEquiv` returns the underlying linear map. -/
@[simp]
theorem trivialEquiv_apply (f : Hom R C M N) :
    trivialEquiv (R := R) (C := C) (M := M) (N := N) f = f.toLinearMap :=
  rfl

/-- The inverse of `trivialEquiv` sends a linear map to the corresponding morphism of
trivial comodules. -/
@[simp]
theorem trivialEquiv_symm_apply (f : M →ₗ[R] N) :
    (trivialEquiv (R := R) (C := C) (M := M) (N := N)).symm f =
      ofTrivial (R := R) (C := C) f :=
  rfl

/-- Pointwise form of `trivialEquiv_symm_apply`. -/
@[simp]
theorem trivialEquiv_symm_apply_apply (f : M →ₗ[R] N) (m : M) :
    (trivialEquiv (R := R) (C := C) (M := M) (N := N)).symm f m = f m :=
  rfl

end Hom

end Trivial

end Comodule

end TauCeti
