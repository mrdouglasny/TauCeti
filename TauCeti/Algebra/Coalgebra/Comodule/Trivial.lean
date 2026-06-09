/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.GroupLike
import TauCeti.Algebra.Coalgebra.ComoduleCat

/-!
# Trivial comodules from group-like elements

This file adds the basic one-dimensional right comodule attached to a group-like element
of a coalgebra. For a group-like element `g : C`, the base semiring `R` is a right
`C`-comodule through the coaction `r ↦ r ⊗ g`. For a bialgebra, the group-like element
`1 : C` gives the usual trivial comodule, and the bialgebra unit `R → C` is a morphism
from this trivial comodule to the regular right comodule.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": the representation category needs its trivial object and the
canonical map from the trivial representation into the regular representation before the
tensor-product and finite-dimensional APIs are built.

## Main definitions

* `TauCeti.Comodule.instGroupLike`: the right comodule on `R` attached to a group-like
  element.
* `TauCeti.Comodule.groupLikeToSelf`: the canonical morphism from the `g`-trivial comodule
  to the regular comodule.
* `TauCeti.Comodule.instBase`: the trivial right comodule on `R` for a bialgebra.
* `TauCeti.Comodule.baseToSelf`: the bialgebra unit as a comodule morphism
  `R ⟶ C`.
* `TauCeti.Comodule.IsCoinvariantFor`: vectors whose coaction is `m ⊗ g`.
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

section GroupLike

variable (R : Type u) (C : Type v) [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The coaction on the base semiring attached to a group-like element. -/
def groupLikeCoact (g : GroupLike R C) : R →ₗ[R] R ⊗[R] C :=
  (TensorProduct.mk R R C).flip g

/-- The right comodule on the base semiring attached to a group-like element.

The coaction sends `r : R` to `r ⊗ g`. This is a definition rather than a global instance,
because the chosen group-like element is not inferable from the type `R`. -/
@[reducible]
def instGroupLike (g : GroupLike R C) : Comodule R C R where
  coact := groupLikeCoact R C g
  coassoc := by
    ext
    simp [groupLikeCoact, g.2.comul_eq_tmul_self]
  lTensor_counit_comp_coact := by
    ext
    simp [groupLikeCoact, g.2.counit_eq_one]

/-- The coaction attached to a group-like element is `r ↦ r ⊗ g`. -/
@[simp]
theorem instGroupLike_coact (g : GroupLike R C) :
    @coact R C R _ _ _ _ _ _ (instGroupLike R C g) = groupLikeCoact R C g :=
  rfl

/-- The coaction attached to a group-like element sends `r` to `r ⊗ g`. -/
@[simp]
theorem groupLikeCoact_apply (g : GroupLike R C) (r : R) :
    groupLikeCoact R C g r = r ⊗ₜ[R] (g : C) :=
  rfl

section CoinvariantFor

variable {M : Type*} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Morphisms out of the `g`-trivial comodule. -/
abbrev HomFromGroupLike (g : GroupLike R C) :=
  letI : Comodule R C R := instGroupLike R C g
  Hom R C R M

/-- A vector of a right comodule is coinvariant for a group-like element `g` if its
coaction is `m ⊗ g`.

Equivalently, it determines a comodule morphism from the `g`-trivial comodule to `M`. -/
def IsCoinvariantFor (g : GroupLike R C) (m : M) : Prop :=
  coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C)

/-- Restatement of `IsCoinvariantFor` as a coaction equality. -/
@[simp]
theorem isCoinvariantFor_iff (g : GroupLike R C) (m : M) :
    IsCoinvariantFor (R := R) (C := C) g m ↔
      coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (g : C) :=
  Iff.rfl

/-- The zero vector is coinvariant for any group-like element. -/
theorem isCoinvariantFor_zero (g : GroupLike R C) :
    IsCoinvariantFor (R := R) (C := C) g (0 : M) := by
  simp [IsCoinvariantFor]

/-- Vectors coinvariant for the same group-like element are closed under addition. -/
theorem IsCoinvariantFor.add {g : GroupLike R C} {m n : M}
    (hm : IsCoinvariantFor (R := R) (C := C) g m)
    (hn : IsCoinvariantFor (R := R) (C := C) g n) :
    IsCoinvariantFor (R := R) (C := C) g (m + n) := by
  rw [IsCoinvariantFor] at hm hn ⊢
  rw [map_add, hm, hn, TensorProduct.add_tmul]

/-- Vectors coinvariant for a group-like element are closed under scalar multiplication. -/
theorem IsCoinvariantFor.smul (r : R) {g : GroupLike R C} {m : M}
    (hm : IsCoinvariantFor (R := R) (C := C) g m) :
    IsCoinvariantFor (R := R) (C := C) g (r • m) := by
  rw [IsCoinvariantFor] at hm ⊢
  rw [map_smul, hm, TensorProduct.smul_tmul']

/-- A comodule morphism out of the `g`-trivial comodule sends `1` to a vector coinvariant
for `g`. -/
theorem apply_one_isCoinvariantFor (g : GroupLike R C)
    (f : HomFromGroupLike (R := R) (C := C) (M := M) g) :
    IsCoinvariantFor (R := R) (C := C) g (f (1 : R)) := by
  letI := instGroupLike R C g
  rw [IsCoinvariantFor]
  exact (Hom.map_coact_apply f (1 : R)).symm

/-- The comodule morphism from the `g`-trivial comodule determined by a `g`-coinvariant
vector. -/
def ofCoinvariantFor (g : GroupLike R C) (m : M)
    (hm : IsCoinvariantFor (R := R) (C := C) g m) :
    HomFromGroupLike (R := R) (C := C) (M := M) g := by
  letI : Comodule R C R := instGroupLike R C g
  exact
    { toLinearMap :=
        { toFun := fun r => r • m
          map_add' := by
            intro r s
            exact add_smul r s m
          map_smul' := by
            intro r s
            exact mul_smul r s m }
      map_coact := by
        apply LinearMap.ext
        intro r
        exact (IsCoinvariantFor.smul (R := R) (C := C) r hm).symm }

/-- The morphism attached to a `g`-coinvariant vector evaluates by scalar multiplication. -/
@[simp]
theorem ofCoinvariantFor_apply (g : GroupLike R C) (m : M)
    (hm : IsCoinvariantFor (R := R) (C := C) g m) (r : R) :
    ofCoinvariantFor (R := R) (C := C) g m hm r = r • m :=
  by
    simp [ofCoinvariantFor]

/-- The morphism attached to a `g`-coinvariant vector sends `1` to that vector. -/
@[simp]
theorem ofCoinvariantFor_apply_one (g : GroupLike R C) (m : M)
    (hm : IsCoinvariantFor (R := R) (C := C) g m) :
    ofCoinvariantFor (R := R) (C := C) g m hm (1 : R) = m := by
  simp

/-- A morphism from the `g`-trivial comodule is determined by the image of `1`. -/
theorem hom_ext_one_for {g : GroupLike R C}
    {f h : HomFromGroupLike (R := R) (C := C) (M := M) g}
    (hh : f (1 : R) = h (1 : R)) : f = h := by
  letI := instGroupLike R C g
  apply Hom.ext
  intro r
  calc
    f r = r • f (1 : R) := by
      simpa using map_smul f.toLinearMap r (1 : R)
    _ = r • h (1 : R) := by rw [hh]
    _ = h r := by
      simpa using (map_smul h.toLinearMap r (1 : R)).symm

/-- Recover a morphism from the `g`-trivial comodule from its value at `1`. -/
@[simp]
theorem ofCoinvariantFor_apply_one_isCoinvariantFor (g : GroupLike R C)
    (f : HomFromGroupLike (R := R) (C := C) (M := M) g) :
    ofCoinvariantFor (R := R) (C := C) g (f (1 : R)) (apply_one_isCoinvariantFor R C g f) =
      f :=
  hom_ext_one_for (R := R) (C := C) (by simp)

end CoinvariantFor

/-- A group-like element is coinvariant for itself in the regular comodule. -/
theorem groupLike_isCoinvariantFor (g : GroupLike R C) :
    IsCoinvariantFor (R := R) (C := C) g (g : C) := by
  rw [IsCoinvariantFor]
  simp

/-- The canonical morphism from the `g`-trivial comodule to the regular right comodule. -/
def groupLikeToSelf (g : GroupLike R C) : HomFromGroupLike (R := R) (C := C) (M := C) g :=
  ofCoinvariantFor (R := R) (C := C) g (g : C) (groupLike_isCoinvariantFor R C g)

/-- The map `groupLikeToSelf` sends a scalar to the corresponding multiple of `g`. -/
@[simp]
theorem groupLikeToSelf_apply (g : GroupLike R C) (r : R) :
    groupLikeToSelf R C g r = r • (g : C) := by
  simp [groupLikeToSelf]

/-- The map `groupLikeToSelf` sends `1` to `g`. -/
@[simp]
theorem groupLikeToSelf_one (g : GroupLike R C) :
    groupLikeToSelf R C g (1 : R) = (g : C) := by
  simp

end GroupLike

section Bialgebra

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The trivial right comodule on the base semiring of a bialgebra.

The coaction sends `r : R` to `r ⊗ 1`, using the grouplike element `1 : C`. -/
instance instBase : Comodule R C R :=
  instGroupLike R C (1 : GroupLike R C)

/-- The coaction of the trivial right comodule is `r ↦ r ⊗ 1`. -/
@[simp]
theorem instBase_coact :
    coact (R := R) (C := C) (M := R) =
      (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] C).toLinearMap := by
  rfl

/-- The coaction of the trivial right comodule sends `r` to `r ⊗ 1`. -/
@[simp]
theorem instBase_coact_apply (r : R) :
    coact (R := R) (C := C) (M := R) r = r ⊗ₜ[R] (1 : C) :=
  rfl

/-- The coaction of the trivial right comodule is Mathlib's left tensor inclusion. -/
theorem toLinearMap_includeLeft :
    (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] C).toLinearMap =
      coact (R := R) (C := C) (M := R) := by
  rfl

/-- The bialgebra unit is a morphism from the trivial right comodule to the regular right
comodule. -/
def baseToSelf : Hom R C R C :=
  groupLikeToSelf R C (1 : GroupLike R C)

/-- The underlying linear map of `baseToSelf` is the algebra unit. -/
@[simp]
theorem baseToSelf_toLinearMap :
    (baseToSelf R C).toLinearMap = Algebra.linearMap R C :=
  LinearMap.ext fun r => by
    simp [baseToSelf, Algebra.smul_def]

/-- The map `baseToSelf` sends a scalar to the corresponding scalar multiple of `1`. -/
@[simp]
theorem baseToSelf_apply (r : R) : baseToSelf R C r = algebraMap R C r := by
  simp [baseToSelf, Algebra.smul_def]

/-- The map `baseToSelf` sends `1` to `1`. -/
@[simp]
theorem baseToSelf_one : baseToSelf R C (1 : R) = (1 : C) :=
  groupLikeToSelf_one R C (1 : GroupLike R C)

section Coinvariant

variable {M : Type*} [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A vector of a right comodule over a bialgebra is coinvariant if its coaction is
`m ⊗ 1`.

Equivalently, it determines a comodule morphism from the trivial comodule to `M`. -/
abbrev IsCoinvariant (m : M) : Prop :=
  IsCoinvariantFor (R := R) (C := C) (1 : GroupLike R C) m

/-- Restatement of `IsCoinvariant` as a coaction equality. -/
@[simp]
theorem isCoinvariant_iff (m : M) :
    IsCoinvariant (R := R) (C := C) m ↔
      coact (R := R) (C := C) (M := M) m = m ⊗ₜ[R] (1 : C) :=
  Iff.rfl

/-- The zero vector is coinvariant. -/
theorem isCoinvariant_zero : IsCoinvariant (R := R) (C := C) (0 : M) := by
  exact isCoinvariantFor_zero R C (1 : GroupLike R C)

/-- Coinvariant vectors are closed under addition. -/
theorem IsCoinvariant.add {m n : M} (hm : IsCoinvariant (R := R) (C := C) m)
    (hn : IsCoinvariant (R := R) (C := C) n) :
    IsCoinvariant (R := R) (C := C) (m + n) := by
  exact IsCoinvariantFor.add (R := R) (C := C) hm hn

/-- Coinvariant vectors are closed under scalar multiplication. -/
theorem IsCoinvariant.smul (r : R) {m : M} (hm : IsCoinvariant (R := R) (C := C) m) :
    IsCoinvariant (R := R) (C := C) (r • m) := by
  exact IsCoinvariantFor.smul (R := R) (C := C) r hm

/-- A comodule morphism out of the trivial comodule sends `1` to a coinvariant vector. -/
theorem apply_one_isCoinvariant (f : Hom R C R M) :
    IsCoinvariant (R := R) (C := C) (f (1 : R)) := by
  exact apply_one_isCoinvariantFor R C (1 : GroupLike R C) f

/-- The comodule morphism from the trivial comodule determined by a coinvariant vector. -/
abbrev ofCoinvariant (m : M) (hm : IsCoinvariant (R := R) (C := C) m) : Hom R C R M :=
  ofCoinvariantFor (R := R) (C := C) (1 : GroupLike R C) m hm

/-- The morphism attached to a coinvariant vector evaluates by scalar multiplication. -/
@[simp]
theorem ofCoinvariant_apply (m : M) (hm : IsCoinvariant (R := R) (C := C) m) (r : R) :
    ofCoinvariant (R := R) (C := C) m hm r = r • m :=
  by
    simp [ofCoinvariant]

/-- The morphism attached to a coinvariant vector sends `1` to that vector. -/
@[simp]
theorem ofCoinvariant_apply_one (m : M) (hm : IsCoinvariant (R := R) (C := C) m) :
    ofCoinvariant (R := R) (C := C) m hm (1 : R) = m := by
  simp

/-- A morphism from the trivial comodule is determined by the image of `1`. -/
theorem hom_ext_one {f g : Hom R C R M} (h : f (1 : R) = g (1 : R)) : f = g := by
  exact hom_ext_one_for (R := R) (C := C) h

/-- Recover a morphism from the trivial comodule from its value at `1`. -/
@[simp]
theorem ofCoinvariant_apply_one_isCoinvariant (f : Hom R C R M) :
    ofCoinvariant (R := R) (C := C) (f (1 : R)) (apply_one_isCoinvariant R C f) = f :=
  hom_ext_one (R := R) (C := C) (by simp)

end Coinvariant

end Bialgebra

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
    Comodule.coact (R := R) (C := C) (M := trivial R C) =
      (Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[R] C).toLinearMap :=
  rfl

end ComoduleCat

end TauCeti
