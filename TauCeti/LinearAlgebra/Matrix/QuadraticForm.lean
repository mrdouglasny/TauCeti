/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms associated to real matrices

This file records elementary API for Mathlib's quadratic form attached to a real square
matrix.

## Main declarations

* `TauCeti.Matrix.toQuadraticForm'_eq_dotProduct`: the matrix quadratic form is the
  dot-product expression `ξᵀ A ξ`.
* `TauCeti.Matrix.toQuadraticForm'_transpose`: transposition preserves the associated
  quadratic form.
* `TauCeti.Matrix.toQuadraticForm'_smul`: scalar multiplication of coefficient matrices
  scales the associated quadratic form.
-/

namespace TauCeti

namespace Matrix

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ A.mulVec ξ := by
  rw [_root_.Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, _root_.Matrix.toLinearMap₂'_apply']

/-- Transposition does not change the quadratic form associated to a real matrix. -/
@[simp]
lemma toQuadraticForm'_transpose (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.transpose.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    _root_.Matrix.dotProduct_transpose_mulVec]

/-- Matrix quadratic forms are linear in scalar multiplication of the coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_smul (c : ℝ) (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • A).toQuadraticForm' ξ = c * A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    _root_.Matrix.smul_mulVec, _root_.dotProduct_smul]
  simp [smul_eq_mul]

end Matrix

end TauCeti
