/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Trace-form diagonalisation for square-root bases

The effective discriminant bound `|d_K| ≤ |disc b|` (already in
`TauCeti/NumberTheory/EffectiveBounds/Discriminant.lean`) is only useful once one can
*evaluate* `disc b` on a concrete basis. The cheapest bases of a quadratic field are the
square-root bases `{1, x}` with `x² ∈ K`, and on those the trace form is diagonal: the
off-diagonal entry `Tr(1 · x) = Tr x` vanishes because an element whose square lies in the
base field has trace zero.

This file supplies that trace-vanishing criterion and the resulting discriminant formula.

## Main results

* `TauCeti.Algebra.trace_eq_zero_of_sq_mem_range`: if `x² ∈ K` (as an element of a finite
  field extension `L / K`) but `x ∉ K`, then `Tr_{L/K} x = 0`.
* `TauCeti.NumberField.trace_eq_zero_of_sq_ratCast`: the number-field specialisation, for
  `x` in a number field `K` with `x² = (q : K)` rational and `x` irrational.
* `TauCeti.Algebra.discr_one_self_eq_of_sq`: for a quadratic extension `L / K` and
  `x ∉ K` with `x² = a ∈ K`, the trace-form discriminant of the basis `{1, x}` is `4 a`.

The two `example`s at the end exercise the API on `ℂ / ℝ` (degree two): `Tr_{ℂ/ℝ} I = 0`
and `disc ℝ {1, I} = -4`, mirroring the roadmap's `ℚ(i)` worked example.

## Provenance

The trace-vanishing criterion migrates `trace_eq_zero_of_sq_ratCast` from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where it diagonalises the trace form on square-root bases; the criterion is
restated here over an arbitrary finite field extension, with the rational version kept as a
direct corollary.
-/

open Module Polynomial

namespace TauCeti

namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- If `x` lies in a finite extension `L / K`, its square lies in `K`, but `x` itself does
not, then the trace `Tr_{L/K} x` vanishes. Indeed the minimal polynomial of such an `x` is
`X² - a`, whose subleading coefficient is zero, and the trace is `[L : K(x)]` times that
coefficient. -/
theorem trace_eq_zero_of_sq_mem_range {x : L} {a : K} (hx2 : x ^ 2 = algebraMap K L a)
    (hx : x ∉ (algebraMap K L).range) : Algebra.trace K L x = 0 := by
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  -- `x` is a root of the monic quadratic `X² - C a`.
  have haeval : (Polynomial.aeval x) (X ^ 2 - C a) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx2, sub_self]
  have hmonic : (X ^ 2 - C a : K[X]).Monic := monic_X_pow_sub_C a (by norm_num)
  have hdvd : minpoly K x ∣ (X ^ 2 - C a) := minpoly.dvd K x haeval
  -- `x ∉ K` forces the minimal polynomial to have degree at least two, hence to *be* it.
  have hge : 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff hint).mpr hx
  have hmin : (X ^ 2 - C a : K[X]) = minpoly K x :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [natDegree_X_pow_sub_C]; exact hge)
  -- The subleading coefficient of `X² - C a` is zero.
  have hnext : (X ^ 2 - C a : K[X]).nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by rw [natDegree_X_pow_sub_C]; norm_num),
      natDegree_X_pow_sub_C]
    simp [coeff_X_pow]
  rw [trace_eq_finrank_mul_minpoly_nextCoeff K x, ← hmin, hnext, neg_zero, mul_zero]

/-- For a quadratic extension `L / K` and an element `x ∉ K` whose square is `a ∈ K`, the
trace-form discriminant of the square-root basis `{1, x}` equals `4 a`: the trace form is
diagonal with entries `Tr 1 = 2` and `Tr x² = 2 a`. -/
theorem discr_one_self_eq_of_sq {x : L} {a : K} (hfin : finrank K L = 2)
    (hx2 : x ^ 2 = algebraMap K L a) (hx : x ∉ (algebraMap K L).range) :
    Algebra.discr K ![1, x] = 4 * a := by
  have htr0 : Algebra.trace K L x = 0 := trace_eq_zero_of_sq_mem_range hx2 hx
  have e00 : Algebra.traceMatrix K ![1, x] 0 0 = 2 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, mul_one]
    rw [show (1 : L) = algebraMap K L 1 from (map_one _).symm, Algebra.trace_algebraMap, hfin]
    simp
  have e11 : Algebra.traceMatrix K ![1, x] 1 1 = 2 * a := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show x * x = algebraMap K L a from by rw [← pow_two]; exact hx2,
      Algebra.trace_algebraMap, hfin]
    simp [nsmul_eq_mul]
  have e01 : Algebra.traceMatrix K ![1, x] 0 1 = 0 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    exact htr0
  have e10 : Algebra.traceMatrix K ![1, x] 1 0 = 0 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    exact htr0
  rw [Algebra.discr_def, Matrix.det_fin_two, e00, e11, e01, e10]
  ring

end Algebra

namespace NumberField

/-- **Trace-zero criterion for square-root generators.** In a number field `K`, an element
`x` whose square is a rational `q` but which is itself irrational has trace zero. This is
the form that diagonalises the trace form on a square-root basis of a quadratic field. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {q : ℚ}
    (hx2 : x ^ 2 = (q : K)) (hx : ∀ r : ℚ, (r : K) ≠ x) : Algebra.trace ℚ K x = 0 := by
  refine TauCeti.Algebra.trace_eq_zero_of_sq_mem_range (a := q) ?_ ?_
  · rw [hx2, eq_ratCast]
  · rintro ⟨r, hr⟩
    rw [eq_ratCast] at hr
    exact hx r hr

end NumberField

namespace Algebra

/-- `Complex.I` squares to the real number `-1`, so its trace over `ℝ` vanishes. -/
example : Algebra.trace ℝ ℂ Complex.I = 0 := by
  refine trace_eq_zero_of_sq_mem_range (a := -1) ?_ ?_
  · rw [Complex.I_sq]; simp
  · rintro ⟨r, hr⟩
    simpa [Complex.ext_iff, Complex.I_im] using congrArg Complex.im hr

/-- The trace-form discriminant of the basis `{1, I}` of `ℂ` over `ℝ` is `-4`, recovering
`|disc {1, i}| = 4` of the roadmap's `ℚ(i)` worked example. -/
example : Algebra.discr ℝ ![1, Complex.I] = -4 := by
  rw [discr_one_self_eq_of_sq (a := -1) Complex.finrank_real_complex]
  · norm_num
  · rw [Complex.I_sq]; simp
  · rintro ⟨r, hr⟩
    simpa [Complex.ext_iff, Complex.I_im] using congrArg Complex.im hr

end Algebra

end TauCeti
