/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.GroupLike
import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Trivial comodules

For a bialgebra `C` over `R`, every `R`-module `M` has a right `C`-comodule structure whose
coaction is `m ↦ m ⊗ 1`.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target "Comodules over
a coalgebra/Hopf algebra": the representation category of an affine group scheme needs the
trivial representation, and over a Hopf algebra that representation is exactly this trivial
comodule.

## Main definitions

* `TauCeti.Comodule.Trivial`: a wrapper carrying the right coaction by the bialgebra unit.
* `TauCeti.Comodule.trivialCoact`: the specialization `m ↦ m ⊗ 1`.
* `TauCeti.Comodule.Hom.toTrivial`: build a morphism into a trivial comodule from the
  concrete coaction-compatibility equation.

## References

Internally, the proofs use Mathlib's group-like element API and the bialgebra fact that `1`
is group-like.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]

section GroupLike

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-- The coaction map associated to a group-like element: `m ↦ m ⊗ g`. -/
private def groupLikeCoact (g : GroupLike R C) : M →ₗ[R] M ⊗[R] C :=
  (TensorProduct.mk R M C).flip g

@[simp]
private lemma groupLikeCoact_apply (g : GroupLike R C) (m : M) :
    groupLikeCoact (R := R) (C := C) (M := M) g m = m ⊗ₜ[R] (g : C) :=
  rfl

/-- Coaction by a group-like element is coassociative, as an equality of linear maps on the
underlying module. -/
@[simp]
private lemma groupLikeCoact_coassoc (g : GroupLike R C) :
    TensorProduct.assoc R M C C ∘ₗ (groupLikeCoact (R := R) (C := C) (M := M) g).rTensor C ∘ₗ
        groupLikeCoact (R := R) (C := C) (M := M) g =
      Coalgebra.comul.lTensor M ∘ₗ groupLikeCoact (R := R) (C := C) (M := M) g := by
  ext m
  simp [groupLikeCoact]

/-- Coaction by a group-like element satisfies the counit law, as an equality of linear maps
on the underlying module. -/
@[simp]
private lemma lTensor_counit_comp_groupLikeCoact (g : GroupLike R C) :
    Coalgebra.counit.lTensor M ∘ₗ groupLikeCoact (R := R) (C := C) (M := M) g =
      (TensorProduct.mk R M R).flip 1 := by
  ext m
  simp [groupLikeCoact]

end GroupLike

section BialgebraUnit

variable [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- A type synonym for an `R`-module equipped with the trivial right coaction over a
bialgebra `C`.

Use this wrapper when the same underlying module already has, or may later have, another
comodule structure. -/
def Trivial (_ : Type u) (_ : Type v) (M : Type w) :=
  M

namespace Trivial

instance : AddCommMonoid (Trivial R C M) :=
  inferInstanceAs (AddCommMonoid M)

instance : Module R (Trivial R C M) :=
  inferInstanceAs (Module R M)

end Trivial

/-- The coaction map of the trivial right comodule over a bialgebra: `m ↦ m ⊗ 1`. -/
def trivialCoact : M →ₗ[R] M ⊗[R] C :=
  groupLikeCoact (R := R) (C := C) (M := M) (1 : GroupLike R C)

@[simp]
lemma trivialCoact_apply (m : M) : trivialCoact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] 1 :=
  rfl

/-- The trivial coaction is coassociative, as an equality of linear maps on the underlying
module. -/
@[simp]
lemma trivialCoact_coassoc :
    TensorProduct.assoc R M C C ∘ₗ (trivialCoact (R := R) (C := C) (M := M)).rTensor C ∘ₗ
        trivialCoact (R := R) (C := C) (M := M) =
      Coalgebra.comul.lTensor M ∘ₗ trivialCoact (R := R) (C := C) (M := M) :=
  groupLikeCoact_coassoc (R := R) (C := C) (M := M) (1 : GroupLike R C)

/-- The trivial coaction satisfies the counit law, as an equality of linear maps on the
underlying module. -/
@[simp]
lemma lTensor_counit_comp_trivialCoact :
    Coalgebra.counit.lTensor M ∘ₗ trivialCoact (R := R) (C := C) (M := M) =
      (TensorProduct.mk R M R).flip 1 :=
  lTensor_counit_comp_groupLikeCoact (R := R) (C := C) (M := M) (1 : GroupLike R C)

/-- The trivial right comodule on an `R`-module, using the unit of a bialgebra. -/
instance instTrivial : Comodule R C (Trivial R C M) where
  coact := trivialCoact (R := R) (C := C) (M := Trivial R C M)
  coassoc :=
    trivialCoact_coassoc (R := R) (C := C) (M := Trivial R C M)
  lTensor_counit_comp_coact :=
    lTensor_counit_comp_trivialCoact (R := R) (C := C) (M := Trivial R C M)

@[simp]
lemma coact_trivial :
    coact (R := R) (C := C) (M := Trivial R C M) =
      trivialCoact (R := R) (C := C) (M := Trivial R C M) :=
  rfl

/-- In the trivial comodule, the coaction of `m` is `m ⊗ 1`. -/
@[simp]
lemma coact_trivial_apply (m : Trivial R C M) :
    coact (R := R) (C := C) (M := Trivial R C M) m = m ⊗ₜ[R] 1 :=
  rfl

namespace Hom

section ToTrivial

variable [Comodule R C M]

/-- Build a comodule morphism into a trivial comodule from the concrete compatibility
condition with the trivial coaction. -/
def toTrivial (f : M →ₗ[R] N)
    (hf : ∀ m, TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := M) m) =
      f m ⊗ₜ[R] (1 : C)) :
    Hom R C M (Trivial R C N) where
  toLinearMap := f
  map_coact := by
    ext m
    exact hf m

@[simp]
lemma toTrivial_apply (f : M →ₗ[R] N)
    (hf : ∀ m, TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := M) m) =
      f m ⊗ₜ[R] (1 : C)) (m : M) :
    toTrivial (R := R) (C := C) f hf m = f m :=
  rfl

@[simp]
lemma toTrivial_toLinearMap (f : M →ₗ[R] N)
    (hf : ∀ m, TensorProduct.map f LinearMap.id (coact (R := R) (C := C) (M := M) m) =
      f m ⊗ₜ[R] (1 : C)) :
    (toTrivial (R := R) (C := C) f hf).toLinearMap = f :=
  rfl

end ToTrivial

/-- A linear map between trivial comodules is automatically a comodule morphism. -/
def trivialMap (f : M →ₗ[R] N) : Hom R C (Trivial R C M) (Trivial R C N) :=
  toTrivial (R := R) (C := C) f fun m => by
    simp

@[simp]
lemma trivialMap_apply (f : M →ₗ[R] N) (m : Trivial R C M) :
    trivialMap (R := R) (C := C) f m = f m :=
  rfl

@[simp]
lemma trivialMap_toLinearMap (f : M →ₗ[R] N) :
    (trivialMap (R := R) (C := C) f).toLinearMap = f :=
  rfl

@[simp]
lemma trivialMap_id :
    trivialMap (R := R) (C := C) (M := M) (N := M) LinearMap.id =
      id R C (Trivial R C M) := by
  ext m
  rfl

/-- Trivial-comodule maps preserve composition of the underlying linear maps. -/
@[simp]
lemma trivialMap_comp {P : Type*} [AddCommMonoid P] [Module R P] (g : N →ₗ[R] P)
    (f : M →ₗ[R] N) :
    trivialMap (R := R) (C := C) (M := M) (N := P) (g.comp f) =
      comp (trivialMap (R := R) (C := C) (M := N) (N := P) g)
        (trivialMap (R := R) (C := C) (M := M) (N := N) f) := by
  ext m
  rfl

end Hom

end BialgebraUnit

end Comodule

end TauCeti
