/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.Hom
import TauCeti.Algebra.Coalgebra.ComoduleCat

/-!
# The trivial comodule over a bialgebra

This file adds the basic one-dimensional right comodule attached to a bialgebra. For a
bialgebra `C`, the base semiring `R` is a right `C`-comodule through the coaction
`r ↦ r ⊗ 1`. The bialgebra unit `R → C` is then a morphism from this trivial comodule to
the regular right comodule.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": the representation category needs its trivial object and the
canonical map from the trivial representation into the regular representation before the
tensor-product and finite-dimensional APIs are built.

## Main definitions

* `TauCeti.Comodule.instBase`: the trivial right comodule on `R`.
* `TauCeti.Comodule.baseToSelf`: the bialgebra unit as a comodule morphism
  `R ⟶ C`.
* `TauCeti.Comodule.IsCoinvariant`: vectors whose coaction is `m ⊗ 1`.
* `TauCeti.Comodule.ofCoinvariant`: a coinvariant vector as a morphism out of the
  trivial comodule.
* `TauCeti.ComoduleCat.trivial`: the bundled trivial comodule.

## References

This follows the standard trivial-comodule construction for a bialgebra; see for example
Sweedler, *Hopf Algebras*, Chapter 2.
-/

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C]

/-- The coaction of the trivial right comodule on the base semiring of a bialgebra. -/
def baseCoact [Algebra R C] : R →ₗ[R] R ⊗[R] C :=
  (TensorProduct.mk R R C).flip 1

variable [Bialgebra R C]

/-- The trivial right comodule on the base semiring of a bialgebra.

The coaction sends `r : R` to `r ⊗ 1`, using the grouplike element `1 : C`. -/
instance instBase : Comodule R C R where
  coact := baseCoact R C
  coassoc := by
    ext
    simp [baseCoact, Algebra.TensorProduct.one_def]
  lTensor_counit_comp_coact := by
    ext
    simp [baseCoact]

/-- The coaction of the trivial right comodule is `r ↦ r ⊗ 1`. -/
@[simp]
theorem instBase_coact : coact (R := R) (C := C) (M := R) = baseCoact R C :=
  rfl

/-- The coaction of the trivial right comodule sends `r` to `r ⊗ 1`. -/
@[simp]
theorem baseCoact_apply (r : R) : baseCoact R C r = r ⊗ₜ[R] (1 : C) :=
  rfl

/-- The coaction of the trivial right comodule, evaluated at a scalar. -/
@[simp]
theorem instBase_coact_apply (r : R) :
    coact (R := R) (C := C) (M := R) r = r ⊗ₜ[R] (1 : C) :=
  rfl

/-- The bialgebra unit as a linear map from the trivial comodule to the regular comodule. -/
def baseToSelfLinearMap : R →ₗ[R] C :=
  Algebra.linearMap R C

/-- The bialgebra unit is a morphism from the trivial right comodule to the regular right
comodule. -/
def baseToSelf : Hom R C R C where
  toLinearMap := baseToSelfLinearMap R C
  map_coact := by
    ext
    simp [baseToSelfLinearMap, Algebra.TensorProduct.one_def]

/-- The underlying linear map of `baseToSelf` is the algebra unit. -/
@[simp]
theorem baseToSelf_toLinearMap :
    (baseToSelf R C).toLinearMap = baseToSelfLinearMap R C :=
  rfl

/-- The map `baseToSelf` sends a scalar to the corresponding scalar multiple of `1`. -/
@[simp]
theorem baseToSelf_apply (r : R) : baseToSelf R C r = algebraMap R C r :=
  rfl

/-- The map `baseToSelf` sends `1` to `1`. -/
@[simp]
theorem baseToSelf_one : baseToSelf R C (1 : R) = (1 : C) :=
  map_one (algebraMap R C)

section Coinvariant

variable {M : Type*} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A vector of a right comodule over a bialgebra is coinvariant if its coaction is
`m ⊗ 1`.

Equivalently, it is a copy of the trivial comodule inside `M`; the lemma
`ofCoinvariant_apply_one` below makes this precise in one direction. -/
def IsCoinvariant (m : M) : Prop :=
  coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C)

/-- Restatement of `IsCoinvariant` as a coaction equality. -/
theorem isCoinvariant_iff (m : M) :
    IsCoinvariant (R := R) (C := C) m ↔
      coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

/-- The zero vector is coinvariant. -/
theorem isCoinvariant_zero : IsCoinvariant (R := R) (C := C) (0 : M) := by
  simp [IsCoinvariant]

/-- Coinvariant vectors are closed under addition. -/
theorem IsCoinvariant.add {m n : M} (hm : IsCoinvariant (R := R) (C := C) m)
    (hn : IsCoinvariant (R := R) (C := C) n) :
    IsCoinvariant (R := R) (C := C) (m + n) := by
  rw [IsCoinvariant] at hm hn ⊢
  rw [map_add, hm, hn, TensorProduct.add_tmul]

/-- Coinvariant vectors are closed under scalar multiplication. -/
theorem IsCoinvariant.smul (r : R) {m : M} (hm : IsCoinvariant (R := R) (C := C) m) :
    IsCoinvariant (R := R) (C := C) (r • m) := by
  rw [IsCoinvariant] at hm ⊢
  rw [map_smul, hm]
  rfl

/-- A comodule morphism out of the trivial comodule sends `1` to a coinvariant vector. -/
theorem apply_one_isCoinvariant (f : Hom R C R M) :
    IsCoinvariant (R := R) (C := C) (f (1 : R)) := by
  rw [IsCoinvariant]
  exact (Hom.map_coact_apply f (1 : R)).symm

/-- The comodule morphism from the trivial comodule determined by a coinvariant vector. -/
def ofCoinvariant (m : M) (hm : IsCoinvariant (R := R) (C := C) m) : Hom R C R M where
  toLinearMap :=
    { toFun := fun r => r • m
      map_add' := by
        intro r s
        exact add_smul r s m
      map_smul' := by
        intro r s
        exact mul_smul r s m }
  map_coact := by
    ext
    simpa [baseCoact] using hm.symm

/-- The morphism attached to a coinvariant vector evaluates by scalar multiplication. -/
@[simp]
theorem ofCoinvariant_apply (m : M) (hm : IsCoinvariant (R := R) (C := C) m) (r : R) :
    ofCoinvariant (R := R) (C := C) m hm r = r • m :=
  rfl

/-- The morphism attached to a coinvariant vector sends `1` to that vector. -/
@[simp]
theorem ofCoinvariant_apply_one (m : M) (hm : IsCoinvariant (R := R) (C := C) m) :
    ofCoinvariant (R := R) (C := C) m hm (1 : R) = m := by
  simp

/-- A morphism from the trivial comodule is determined by the image of `1`. -/
theorem hom_ext_one {f g : Hom R C R M} (h : f (1 : R) = g (1 : R)) : f = g := by
  ext r
  calc
    f r = r • f (1 : R) := by
      simpa using map_smul f.toLinearMap r (1 : R)
    _ = r • g (1 : R) := by rw [h]
    _ = g r := by
      simpa using (map_smul g.toLinearMap r (1 : R)).symm

end Coinvariant

end Comodule

namespace ComoduleCat

universe u v

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The bundled trivial right comodule over a bialgebra. -/
abbrev trivial : ComoduleCat.{u, v, u} R C :=
  of R C R

/-- The coaction on the bundled trivial comodule is `r ↦ r ⊗ 1`. -/
@[simp]
theorem trivial_coact :
    Comodule.coact (R := R) (C := C) (M := trivial R C) = Comodule.baseCoact R C :=
  rfl

end ComoduleCat

end TauCeti
