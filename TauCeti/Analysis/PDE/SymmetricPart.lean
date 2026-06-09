/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.UniformEllipticity
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetric parts of PDE coefficient matrices

For a real divergence-form coefficient matrix `A`, the quadratic expression
`ξᵀ A ξ` only depends on the symmetric part `(A + Aᵀ) / 2`. This file records that
bookkeeping in the explicit-constant API from `TauCeti.Analysis.PDE.UniformEllipticity`.

The main result is `UniformlyEllipticOn.symmetricPart`: a uniformly elliptic, possibly
nonsymmetric coefficient field has a symmetric part that is uniformly elliptic with the
same constants. This is a small prerequisite for the PDE roadmap's energy-form and
Lax--Milgram lane, where coercivity comes from the symmetric quadratic part while
boundedness still controls the full bilinear form.

## Main declarations

* `TauCeti.PDE.symmetricPart`: Mathlib's self-adjoint part, specialized to real matrices.
* `TauCeti.PDE.skewPart`: Mathlib's skew-adjoint part, specialized to real matrices.
* `TauCeti.PDE.toQuadraticForm'_symmetricPart`: symmetrization preserves `ξᵀ A ξ`.
* `TauCeti.PDE.UniformlyEllipticOn.symmetricPart`: uniform ellipticity descends to the
  symmetric part with unchanged constants.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric part `(A + Aᵀ) / 2` of a real matrix. -/
noncomputable def symmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  selfAdjointPart ℝ A

/-- The skew-symmetric part `(A - Aᵀ) / 2` of a real matrix. -/
noncomputable def skewPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  skewAdjointPart ℝ A

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part is Mathlib's self-adjoint part, coerced back to matrices. -/
lemma symmetricPart_def (A : Matrix n n ℝ) :
    symmetricPart A = (selfAdjointPart ℝ A : Matrix n n ℝ) :=
  rfl

omit [Fintype n] [DecidableEq n] in
/-- The skew-symmetric part is Mathlib's skew-adjoint part, coerced back to matrices. -/
lemma skewPart_def (A : Matrix n n ℝ) :
    skewPart A = (skewAdjointPart ℝ A : Matrix n n ℝ) :=
  rfl

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part of a real matrix, written with transpose. -/
lemma symmetricPart_eq (A : Matrix n n ℝ) :
    symmetricPart A = (2 : ℝ)⁻¹ • (A + Aᵀ) := by
  rw [symmetricPart, selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [invOf_eq_inv]

omit [Fintype n] [DecidableEq n] in
/-- The skew-symmetric part of a real matrix, written with transpose. -/
lemma skewPart_eq (A : Matrix n n ℝ) :
    skewPart A = (2 : ℝ)⁻¹ • (A - Aᵀ) := by
  rw [skewPart, skewAdjointPart_apply_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [invOf_eq_inv]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise formula for the symmetric part of a real matrix. -/
lemma symmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    symmetricPart A i j = (2 : ℝ)⁻¹ * (A i j + A j i) := by
  rw [symmetricPart_eq]
  simp [smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise formula for the skew-symmetric part of a real matrix. -/
lemma skewPart_apply (A : Matrix n n ℝ) (i j : n) :
    skewPart A i j = (2 : ℝ)⁻¹ * (A i j - A j i) := by
  rw [skewPart_eq]
  simp [smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part is symmetric. -/
lemma symmetricPart_isSymm (A : Matrix n n ℝ) : (symmetricPart A).IsSymm := by
  rw [symmetricPart_eq]
  exact (Matrix.isSymm_add_transpose_self A).smul (2 : ℝ)⁻¹

omit [Fintype n] [DecidableEq n] in
/-- The transpose of the skew part is its negative. -/
lemma skewPart_transpose (A : Matrix n n ℝ) : (skewPart A)ᵀ = -skewPart A := by
  ext i j
  simp [skewPart_apply, sub_eq_add_neg]
  ring_nf

omit [Fintype n] [DecidableEq n] in
/-- A symmetric matrix is fixed by taking the symmetric part. -/
@[simp]
lemma Matrix.IsSymm.symmetricPart_eq_self {A : Matrix n n ℝ} (hA : A.IsSymm) :
    symmetricPart A = A := by
  ext i j
  rw [symmetricPart_apply]
  have hji : A j i = A i j := hA.apply i j
  rw [hji]
  ring

omit [Fintype n] [DecidableEq n] in
/-- A symmetric matrix has zero skew-symmetric part. -/
@[simp]
lemma Matrix.IsSymm.skewPart_eq_zero {A : Matrix n n ℝ} (hA : A.IsSymm) :
    skewPart A = 0 := by
  ext i j
  rw [skewPart_apply]
  have hji : A j i = A i j := hA.apply i j
  rw [hji]
  simp

omit [Fintype n] [DecidableEq n] in
/-- Taking the symmetric part is idempotent. -/
@[simp]
lemma symmetricPart_symmetricPart (A : Matrix n n ℝ) :
    symmetricPart (symmetricPart A) = symmetricPart A :=
  Matrix.IsSymm.symmetricPart_eq_self (symmetricPart_isSymm A)

omit [Fintype n] [DecidableEq n] in
/-- The skew-symmetric part of the symmetric part is zero. -/
@[simp]
lemma skewPart_symmetricPart (A : Matrix n n ℝ) : skewPart (symmetricPart A) = 0 :=
  Matrix.IsSymm.skewPart_eq_zero (symmetricPart_isSymm A)

omit [Fintype n] [DecidableEq n] in
/-- A matrix is the sum of its symmetric and skew-symmetric parts. -/
@[simp]
lemma symmetricPart_add_skewPart (A : Matrix n n ℝ) : symmetricPart A + skewPart A = A := by
  exact StarModule.selfAdjointPart_add_skewAdjointPart ℝ A

/-- Transposing a real matrix does not change its quadratic form. -/
@[simp]
lemma toQuadraticForm'_transpose (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    Aᵀ.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct]
  exact Matrix.dotProduct_transpose_mulVec A ξ ξ

/-- The skew-symmetric part has zero quadratic form. -/
@[simp]
lemma toQuadraticForm'_skewPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (skewPart A).toQuadraticForm' ξ = 0 := by
  have htranspose := toQuadraticForm'_transpose (skewPart A) ξ
  rw [skewPart_transpose] at htranspose
  have hneg :
      (-skewPart A).toQuadraticForm' ξ = - (skewPart A).toQuadraticForm' ξ := by
    simpa using toQuadraticForm'_smul (-1 : ℝ) (skewPart A) ξ
  linarith

/-- The symmetric part has the same quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_symmetricPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (symmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [symmetricPart_eq, toQuadraticForm'_smul, toQuadraticForm'_eq_dotProduct,
    toQuadraticForm'_eq_dotProduct]
  simp only [add_mulVec, dotProduct_add]
  have htranspose : ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) :=
    Matrix.dotProduct_transpose_mulVec A ξ ξ
  rw [htranspose]
  ring

/-- On the diagonal, the bilinear form attached to the symmetric part agrees with the
bilinear form attached to the original matrix. -/
@[simp]
lemma matrixBilinearForm_symmetricPart_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (symmetricPart A) ξ ξ = matrixBilinearForm A ξ ξ := by
  rw [matrixBilinearForm_self, matrixBilinearForm_self, toQuadraticForm'_symmetricPart]

/-- The bilinear form attached to the symmetric part is the average of the two transposed
placements of the original bilinear form. -/
lemma matrixBilinearForm_symmetricPart_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (symmetricPart A) η ξ =
      (2 : ℝ)⁻¹ * (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) := by
  rw [symmetricPart_eq, matrixBilinearForm_smul_apply, matrixBilinearForm_apply,
    matrixBilinearForm_apply, matrixBilinearForm_apply]
  rw [add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec]

omit [DecidableEq n] in
/-- If a matrix bilinear form is bounded by `Λ`, then the symmetric part is bounded by the
same `Λ`. -/
lemma abs_dotProduct_symmetricPart_mulVec_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (symmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_symmetricPart_apply]
  have hηξ : |matrixBilinearForm A η ξ| ≤ Lam * ‖η‖ * ‖ξ‖ := by
    simpa using hA η ξ
  have hξη : |matrixBilinearForm A ξ η| ≤ Lam * ‖ξ‖ * ‖η‖ := by
    simpa using hA ξ η
  have hnorm_eq : Lam * ‖ξ‖ * ‖η‖ = Lam * ‖η‖ * ‖ξ‖ := by ring
  rw [hnorm_eq] at hξη
  calc
    |(2 : ℝ)⁻¹ * (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η)|
        = (2 : ℝ)⁻¹ * |matrixBilinearForm A η ξ + matrixBilinearForm A ξ η| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    _ ≤ (2 : ℝ)⁻¹ * (|matrixBilinearForm A η ξ| + |matrixBilinearForm A ξ η|) := by
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_nonneg.mpr zero_le_two)
    _ ≤ (2 : ℝ)⁻¹ * (Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (inv_nonneg.mpr zero_le_two)
          · exact hηξ
          · exact hξη
    _ = Lam * ‖η‖ * ‖ξ‖ := by ring

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- Taking the pointwise symmetric part preserves uniform ellipticity with the same
constants. -/
lemma symmetricPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => symmetricPart (a x)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · exact abs_dotProduct_symmetricPart_mulVec_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

end UniformlyEllipticOn

end PDE

end TauCeti
