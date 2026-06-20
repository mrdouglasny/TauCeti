/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup

/-!
# Naturality of multiplicative-group points

This file records that the existing points calculation for the multiplicative group is
natural in the value algebra. For a commutative `R`-algebra `A`, `MultiplicativeGroup`
identifies the convolution points `R[T;T⁻¹] →ₐ[R] A` with the unit group `Aˣ`; post-composing
such a point with an `R`-algebra homomorphism `φ : A →ₐ[R] B` corresponds exactly to applying
`Units.map φ.toMonoidHom`.

This is part of the worked example `𝔾ₘ` from the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, "Worked examples" and Layer 0, "R-points as a
group"). It is the multiplicative analogue of the naturality API for the additive group.

## Main declarations

* `TauCeti.MultiplicativeGroup.unitOfPoint_comp`: post-composition of an algebra map sends the
  associated unit through `Units.map`.
* `TauCeti.MultiplicativeGroup.pointEquiv_comp`: naturality of the plain equivalence from
  algebra maps to units.
* `TauCeti.MultiplicativeGroup.comp_point`: naturality in the inverse direction, from units
  to algebra maps.
* `TauCeti.MultiplicativeGroup.unitOfPoint_mapValue`: post-composition of a point maps the
  associated unit by `Units.map`.
* `TauCeti.MultiplicativeGroup.pointsMulEquiv_mapValue`: naturality of the multiplicative
  equivalence from convolution points to units.
* `TauCeti.MultiplicativeGroup.mapValue_pointsMulEquiv_symm_apply`: naturality in the inverse
  direction, from units to convolution points.

## References

The calculation builds on the Laurent-polynomial Hopf algebra and points equivalence in
`TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup`, and on Mathlib's `Units.map`.
-/

open WithConv
open scoped LaurentPolynomial

namespace TauCeti

namespace MultiplicativeGroup

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]

/-- Reading a Laurent-polynomial point as a unit is natural under post-composition of algebra
maps. -/
@[simp]
theorem unitOfPoint_comp (φ : A →ₐ[R] B) (f : R[T;T⁻¹] →ₐ[R] A) :
    unitOfPoint (φ.comp f) = Units.map φ.toMonoidHom (unitOfPoint f) := by
  ext
  rfl

/-- The plain Laurent-polynomial points equivalence is natural in the value algebra. -/
@[simp]
theorem pointEquiv_comp (φ : A →ₐ[R] B) (f : R[T;T⁻¹] →ₐ[R] A) :
    pointEquiv (R := R) (A := B) (φ.comp f) =
      Units.map φ.toMonoidHom (pointEquiv (R := R) (A := A) f) :=
  unitOfPoint_comp φ f

/-- Naturality of the inverse plain points equivalence in the value algebra. -/
@[simp]
theorem comp_point (φ : A →ₐ[R] B) (u : Aˣ) :
    φ.comp (point (R := R) (A := A) u) =
      point (R := R) (A := B) (Units.map φ.toMonoidHom u) := by
  apply (pointEquiv (R := R) (A := B)).injective
  rw [pointEquiv_comp]
  simp

/-- Reading a multiplicative-group point as a unit is natural in the value algebra:
post-composing the point with an `R`-algebra map applies the induced map on unit groups. -/
@[simp]
theorem unitOfPoint_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    unitOfPoint ((AlgHom.mapValue (H := R[T;T⁻¹]) φ f).ofConv) =
      Units.map φ.toMonoidHom (unitOfPoint f.ofConv) := by
  exact unitOfPoint_comp φ f.ofConv

/-- The `𝔾ₘ` points equivalence is natural in the value algebra. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := R[T;T⁻¹]) φ f) =
      Units.map φ.toMonoidHom (pointsMulEquiv f) :=
  unitOfPoint_mapValue φ f

/-- Naturality of the inverse `𝔾ₘ` points equivalence in the value algebra. -/
@[simp]
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (u : Aˣ) :
    AlgHom.mapValue (H := R[T;T⁻¹]) φ
        ((pointsMulEquiv (R := R) (A := A)).symm u) =
      (pointsMulEquiv (R := R) (A := B)).symm (Units.map φ.toMonoidHom u) := by
  apply (pointsMulEquiv (R := R) (A := B)).injective
  rw [pointsMulEquiv_mapValue]
  rw [(pointsMulEquiv (R := R) (A := A)).apply_symm_apply u]
  exact ((pointsMulEquiv (R := R) (A := B)).apply_symm_apply
    (Units.map φ.toMonoidHom u)).symm

end MultiplicativeGroup

end TauCeti
