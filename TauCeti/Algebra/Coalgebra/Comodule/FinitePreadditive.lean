/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Preadditive structure on finitely generated comodules

This file makes the preadditive structure on the category of finitely generated right
comodules over a coalgebra over a commutative ring available from a finite-comodule import.
The category is a full subcategory of all comodules, so Mathlib transfers the preadditive
structure from `ComoduleCat`.

It also records concrete simp lemmas computing the zero, addition, negation, and subtraction of
finitely generated comodule morphisms through the underlying ambient comodule morphism `.hom`,
and pointwise on elements, so downstream code never has to unfold the full-subcategory transfer.

This is a small Layer 1 prerequisite for the reductive-groups roadmap's finite-dimensional
representation category: additive hom-sets are needed before tensor products, duals, and
Tannakian reconstruction can be built on finitely generated comodules.

## Main declarations

* `TauCeti.FGComoduleCat.hom_zero`, `hom_add`, `hom_neg`, `hom_sub`: the additive-group
  operations on finitely generated comodule morphisms agree with those of the ambient
  `ComoduleCat` morphism underneath.
* `TauCeti.FGComoduleCat.zero_apply`, `add_apply`, `neg_apply`, `sub_apply`: the same
  operations computed pointwise on elements.

## References

This supplies additive-category bookkeeping for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule category should have additive hom-sets before the
rigid monoidal representation category is developed. The transfer mechanism is Mathlib's
`ObjectProperty.FullSubcategory` preadditive instance.
-/

open CategoryTheory

namespace TauCeti

universe u v w

namespace FGComoduleCat

section Semiring

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M N : FGComoduleCat.{u, v, w} R C}

/-- Finitely generated comodule morphisms inherit their additive commutative monoid
structure from ambient comodule morphisms. -/
instance instHomAddCommMonoid : AddCommMonoid (M ⟶ N) where
  zero := ObjectProperty.homMk 0
  add f g := ObjectProperty.homMk (f.hom + g.hom)
  nsmul n f := ObjectProperty.homMk (n • f.hom)
  zero_add f := by
    apply ObjectProperty.hom_ext
    exact zero_add f.hom
  add_zero f := by
    apply ObjectProperty.hom_ext
    exact add_zero f.hom
  add_assoc f g h := by
    apply ObjectProperty.hom_ext
    exact add_assoc f.hom g.hom h.hom
  add_comm f g := by
    apply ObjectProperty.hom_ext
    exact add_comm f.hom g.hom
  nsmul_zero f := by
    apply ObjectProperty.hom_ext
    exact AddMonoid.nsmul_zero f.hom
  nsmul_succ n f := by
    apply ObjectProperty.hom_ext
    exact AddMonoid.nsmul_succ n f.hom

/-- The ambient comodule morphism underlying the zero morphism is the zero morphism. -/
@[simp]
theorem hom_zero : (0 : M ⟶ N).hom = 0 :=
  rfl

/-- The ambient comodule morphism underlying a sum is the sum of the underlying morphisms. -/
@[simp]
theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom :=
  rfl

/-- The zero morphism acts as the zero function. -/
@[simp]
theorem zero_apply (m : M) : (0 : M ⟶ N) m = 0 :=
  rfl

/-- Addition of morphisms acts by pointwise addition. -/
@[simp]
theorem add_apply (f g : M ⟶ N) (m : M) : (f + g) m = f m + g m :=
  rfl

/-- Composition of finitely generated comodule morphisms is additive in the left argument. -/
@[simp]
theorem add_comp {P : FGComoduleCat.{u, v, w} R C} (g h : N ⟶ P) (f : M ⟶ N) :
    (f ≫ (g + h)) = f ≫ g + f ≫ h := by
  apply ObjectProperty.hom_ext
  change Comodule.Hom.comp (g.hom + h.hom) f.hom =
    Comodule.Hom.comp g.hom f.hom + Comodule.Hom.comp h.hom f.hom
  exact Comodule.Hom.add_comp (R := R) (C := C) g.hom h.hom f.hom

/-- Composition of finitely generated comodule morphisms is additive in the right argument. -/
@[simp]
theorem comp_add {P : FGComoduleCat.{u, v, w} R C} (g : N ⟶ P) (f h : M ⟶ N) :
    ((f + h) ≫ g) = f ≫ g + h ≫ g := by
  apply ObjectProperty.hom_ext
  change Comodule.Hom.comp g.hom (f.hom + h.hom) =
    Comodule.Hom.comp g.hom f.hom + Comodule.Hom.comp g.hom h.hom
  exact Comodule.Hom.comp_add (R := R) (C := C) g.hom f.hom h.hom

/-- Composition with a zero finitely generated comodule morphism on the left is zero. -/
@[simp]
theorem zero_comp {P : FGComoduleCat.{u, v, w} R C} (g : N ⟶ P) :
    (0 : M ⟶ N) ≫ g = 0 := by
  apply ObjectProperty.hom_ext
  change Comodule.Hom.comp g.hom 0 = 0
  ext m
  simp

/-- Composition with a zero finitely generated comodule morphism on the right is zero. -/
@[simp]
theorem comp_zero {P : FGComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    f ≫ (0 : N ⟶ P) = 0 := by
  apply ObjectProperty.hom_ext
  change Comodule.Hom.comp 0 f.hom = 0
  ext m
  rfl

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M N : FGComoduleCat.{u, v, w} R C}

/-- The ambient comodule morphism underlying a negation is the negation of the underlying
morphism. -/
@[simp]
theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

/-- The ambient comodule morphism underlying a difference is the difference of the underlying
morphisms. -/
@[simp]
theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom :=
  rfl

/-- Negation of morphisms acts by pointwise negation. -/
@[simp]
theorem neg_apply (f : M ⟶ N) (m : M) : (-f) m = -f m :=
  rfl

/-- Subtraction of morphisms acts by pointwise subtraction. -/
@[simp]
theorem sub_apply (f g : M ⟶ N) (m : M) : (f - g) m = f m - g m :=
  rfl

end Ring

end FGComoduleCat

end TauCeti
