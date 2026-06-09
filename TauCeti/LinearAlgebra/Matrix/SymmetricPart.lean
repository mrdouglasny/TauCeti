/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Symmetric and skew-symmetric parts of real matrices

This file records the real square-matrix API for the decomposition of a matrix into its
symmetric and skew-symmetric parts. The definitions are thin aliases for Mathlib's
`selfAdjointPart` and `skewAdjointPart` star-module projections.
-/

namespace TauCeti

namespace Matrix

open _root_.Matrix

variable {n : Type*}

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ (A *ᵥ ξ) := by
  rw [_root_.Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, _root_.Matrix.toLinearMap₂'_apply']

/-- The symmetric part `(A + Aᵀ) / 2` of a real square matrix. -/
noncomputable def symmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (selfAdjointPart ℝ A : Matrix n n ℝ)

/-- The skew-symmetric part `(A - Aᵀ) / 2` of a real square matrix. -/
noncomputable def skewPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (skewAdjointPart ℝ A : Matrix n n ℝ)

/-- Entrywise formula for the symmetric part of a matrix. -/
@[simp]
lemma symmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    symmetricPart A i j = (2 : ℝ)⁻¹ * (A i j + A j i) := by
  simp [symmetricPart, selfAdjointPart_apply_coe, invOf_eq_inv]

/-- Entrywise formula for the skew-symmetric part of a matrix. -/
@[simp]
lemma skewPart_apply (A : Matrix n n ℝ) (i j : n) :
    skewPart A i j = (2 : ℝ)⁻¹ * (A i j - A j i) := by
  simp [skewPart, skewAdjointPart_apply_coe, invOf_eq_inv]

/-- The symmetric part of a matrix is symmetric. -/
lemma isSymm_symmetricPart (A : Matrix n n ℝ) : (symmetricPart A).IsSymm := by
  ext i j
  simp [add_comm]

/-- The symmetric part is invariant under transpose. -/
@[simp]
lemma symmetricPart_transpose (A : Matrix n n ℝ) :
    symmetricPart Aᵀ = symmetricPart A := by
  ext i j
  simp [add_comm]

/-- The skew-symmetric part changes sign under transpose. -/
@[simp]
lemma skewPart_transpose (A : Matrix n n ℝ) : (skewPart A)ᵀ = -skewPart A := by
  ext i j
  simp [skewPart, sub_eq_add_neg]

/-- A symmetric matrix is equal to its symmetric part. -/
@[simp]
lemma symmetricPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    symmetricPart A = A := by
  ext i j
  rw [symmetricPart_apply, hA.apply]
  ring

/-- The symmetric and skew-symmetric parts add back to the original matrix. -/
@[simp]
lemma symmetricPart_add_skewPart (A : Matrix n n ℝ) : symmetricPart A + skewPart A = A := by
  simpa [symmetricPart, skewPart] using
    (StarModule.selfAdjointPart_add_skewAdjointPart ℝ A)

/-- A matrix and its transpose have the same diagonal bilinear form. -/
lemma dotProduct_transpose_mulVec_self [Fintype n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) := by
  simpa using _root_.Matrix.dotProduct_transpose_mulVec (A := A) ξ ξ

/-- The symmetric part has the same diagonal bilinear form as the original matrix. -/
@[simp]
lemma dotProduct_symmetricPart_mulVec_self [Fintype n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    ξ ⬝ᵥ (symmetricPart A *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) := by
  rw [show symmetricPart A = (2 : ℝ)⁻¹ • (A + Aᵀ) by ext i j; simp [symmetricPart],
    smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add,
    dotProduct_transpose_mulVec_self]
  ring

/-- The skew-symmetric part has zero diagonal bilinear form. -/
@[simp]
lemma dotProduct_skewPart_mulVec_self [Fintype n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    ξ ⬝ᵥ (skewPart A *ᵥ ξ) = 0 := by
  rw [show skewPart A = (2 : ℝ)⁻¹ • (A - Aᵀ) by ext i j; simp [skewPart],
    smul_mulVec, dotProduct_smul, sub_mulVec]
  have htranspose : ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) :=
    dotProduct_transpose_mulVec_self A ξ
  rw [dotProduct_sub, htranspose]
  ring

/-- The symmetric part has the same matrix quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_symmetricPart [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    (symmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  simp [toQuadraticForm'_eq_dotProduct, dotProduct_symmetricPart_mulVec_self]

/-- The skew-symmetric part has zero matrix quadratic form. -/
@[simp]
lemma toQuadraticForm'_skewPart [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    (skewPart A).toQuadraticForm' ξ = 0 := by
  simp [toQuadraticForm'_eq_dotProduct]

end Matrix

end TauCeti
