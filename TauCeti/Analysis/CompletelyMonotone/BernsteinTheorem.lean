/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.TightNormed
public import TauCeti.Analysis.CompletelyMonotone.BernsteinMeasures
public import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Hausdorff--Bernstein--Widder theorem

This file prepares the final representation theorem for completely monotone functions on the
closed half-line. The target is the finite-measure version of the
Hausdorff--Bernstein--Widder theorem: a function continuous at `0` from the right and completely
monotone on `(0, ∞)` is exactly the Laplace transform of a unique finite positive measure on
`ℝ≥0`.

The existing Part-1 infrastructure supplies the Chafaï approximating measures
`chafaiRescaled f n`, their finite total-mass bound, bundled Laplace kernels as bounded
continuous test functions, and Prokhorov extraction wrappers. This file assembles those pieces and
records the remaining analytic gaps explicitly.

One definitional point is important. The current Tau Ceti predicate `IsCompletelyMonotone`
requires `C^∞` regularity on the closed set `[0, ∞)` using derivatives within the closed
half-line. A Laplace transform of an arbitrary finite measure need not have finite derivatives at
`0`, so the finite-measure converse is naturally stated using `IsClosedCompletelyMonotone`, which
means continuity on `[0, ∞)` together with `IsCompletelyMonotoneOnIoi`.

## References

* D. V. Widder, *The Laplace Transform*, Princeton University Press, 1941.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/

public section

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Laplace transforms of finite measures on `ℝ≥0` -/

/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
@[expose] noncomputable def laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. -/
@[simp]
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := rfl

/-- The Laplace kernel is measurable as a function of the measure variable. -/
lemma measurable_laplaceKernel (t : ℝ) :
    Measurable fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- The Laplace kernel is continuous as a function of the measure variable. -/
lemma continuous_laplaceKernel (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ t`, the Laplace kernel is integrable against every finite measure on `ℝ≥0`. -/
lemma integrable_laplaceKernel_of_nonneg (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ)))) μ := by
  convert (laplaceKernelBoundedContinuous ht).integrable μ using 1
  ext x
  simp

/-- The value of the Laplace transform at zero is the total finite mass. -/
@[simp]
lemma laplaceTransform_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    laplaceTransform μ 0 = μ.real univ := by
  simp [laplaceTransform]

/-- The Laplace transform of a positive measure is nonnegative. -/
lemma laplaceTransform_nonneg (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (t : ℝ) :
    0 ≤ laplaceTransform μ t := by
  exact integral_nonneg fun x => Real.exp_nonneg _

/-- Proposition packaging the statement that every finite-measure Laplace transform is continuous
on `[0, ∞)`. -/
@[expose] def LaplaceTransformContinuousOnHalfLine : Prop :=
  ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ → ContinuousOn (laplaceTransform μ) (Ici 0)

/-- Proposition packaging the statement that every finite-measure Laplace transform is completely
monotone on `(0, ∞)`. -/
@[expose] def LaplaceTransformOpenCompletelyMonotone : Prop :=
  ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
    IsCompletelyMonotoneOnIoi (laplaceTransform μ)

/-- Gap statement: finite measures with all moments finite satisfy the stronger existing
`IsCompletelyMonotone` predicate for their Laplace transforms.

Missing argument: closed-half-line differentiation under the integral with moment domination at
`0`. The Mathlib full-neighborhood wrapper
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` is not enough at the endpoint; this needs a
within-set analogue, e.g.
`hasDerivWithinAt_integral_of_dominated_loc_of_deriv_le`, or an equivalent filter-level dominated
convergence proof for the right derivative. -/
@[expose] def LaplaceTransformCompletelyMonotoneOfMoments : Prop :=
  ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
    (∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) →
      IsCompletelyMonotone (laplaceTransform μ)

/-! ## The closed-half-line predicate used by the finite-measure theorem -/

/-- Roadmap-level complete monotonicity on the closed half-line.

This is the classical finite-measure hypothesis: the function is continuous on `[0, ∞)` and
completely monotone on the open half-line `(0, ∞)`. It is weaker at the endpoint than the existing
`IsCompletelyMonotone`, which requires all derivatives within `[0, ∞)` to exist at `0`. -/
@[expose] def IsClosedCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Ici 0) ∧ IsCompletelyMonotoneOnIoi f

namespace IsClosedCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A closed-half-line completely monotone function is continuous on `[0, ∞)`. -/
lemma continuousOn (hf : IsClosedCompletelyMonotone f) : ContinuousOn f (Ici 0) := hf.1

/-- A closed-half-line completely monotone function is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (hf : IsClosedCompletelyMonotone f) :
    IsCompletelyMonotoneOnIoi f := hf.2

/-- The existing strong Tau Ceti predicate implies the roadmap-level closed-half-line predicate. -/
lemma of_isCompletelyMonotone (hf : IsCompletelyMonotone f) :
    IsClosedCompletelyMonotone f :=
  ⟨hf.contDiffOn.continuousOn, hf.isCompletelyMonotoneOnIoi⟩

/-- Closed-half-line complete monotonicity is determined by values on `[0, ∞)`. -/
lemma congr (hf : IsClosedCompletelyMonotone f) (h : EqOn g f (Ici 0)) :
    IsClosedCompletelyMonotone g := by
  refine ⟨hf.continuousOn.congr fun x hx => h hx, ?_⟩
  exact hf.isCompletelyMonotoneOnIoi.congr fun x hx => h (Ioi_subset_Ici_self hx)

end IsClosedCompletelyMonotone

/-! ## Easy direction: finite measures give completely monotone Laplace transforms -/

/-- The Laplace transform of a finite measure on `ℝ≥0` is continuous on `[0, ∞)`.

This is dominated convergence in the parameter `t`, using the constant function `1` as an
integrable dominating function on the half-line. -/
theorem laplaceTransform_continuousOn_halfLine (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ContinuousOn (laplaceTransform μ) (Ici 0) := by
  change ContinuousOn (fun t : ℝ => ∫ x : ℝ≥0, Real.exp (-(t * (x : ℝ))) ∂μ) (Ici 0)
  exact
    continuousOn_of_dominated (μ := μ)
      (F := fun (t : ℝ) (x : ℝ≥0) => Real.exp (-(t * (x : ℝ))))
      (bound := fun _ : ℝ≥0 => (1 : ℝ)) (s := Ici (0 : ℝ))
      (by
        intro t _ht
        exact (continuous_laplaceKernel t).aestronglyMeasurable)
      (by
        intro t ht
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht x.2))
      (integrable_const (1 : ℝ))
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        exact (by fun_prop :
          Continuous fun t : ℝ => Real.exp (-(t * (x : ℝ)))).continuousOn)

/-- The first advertised gap is discharged unconditionally. -/
theorem laplaceTransformContinuousOnHalfLine :
    LaplaceTransformContinuousOnHalfLine := by
  intro μ hμ
  letI := hμ
  exact laplaceTransform_continuousOn_halfLine μ

/-- The `n`-th signed moment kernel integral attached to a Laplace transform.

For `0 < t`, this is the `n`-th ordinary derivative of `laplaceTransform μ` at `t`. -/
@[expose] noncomputable def laplaceMomentTransform (μ : Measure ℝ≥0) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ≥0, (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ))) ∂μ

/-- A polynomial times a decaying exponential is bounded on the closed half-line. -/
lemma exists_bound_pow_mul_exp_neg (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖x ^ n * Real.exp (-(b * x))‖ ≤ C := by
  have hsmall : (fun y : ℝ => y ^ n) =O[atTop] (fun y : ℝ => Real.exp (b * y)) :=
    (isLittleO_pow_exp_pos_mul_atTop n hb).isBigO
  rcases hsmall.bound with ⟨Ctail, hCtail⟩
  have htail : ∀ᶠ y in atTop, ‖y ^ n * Real.exp (-(b * y))‖ ≤ Ctail := by
    filter_upwards [hCtail] with y hy
    have h_exp_ne : Real.exp (b * y) ≠ 0 := Real.exp_ne_zero _
    have hy' : ‖y ^ n‖ / ‖Real.exp (b * y)‖ ≤ Ctail := by
      have hnorm_pos : 0 < ‖Real.exp (b * y)‖ := norm_pos_iff.mpr h_exp_ne
      exact (div_le_iff₀ hnorm_pos).mpr (by simpa [mul_comm] using hy)
    calc
      ‖y ^ n * Real.exp (-(b * y))‖ = ‖y ^ n‖ / ‖Real.exp (b * y)‖ := by
        rw [norm_mul, Real.exp_neg, norm_inv]
        rfl
      _ ≤ Ctail := hy'
  rcases eventually_atTop.1 htail with ⟨R, hR⟩
  set A : ℝ := max R 0 with hA
  obtain ⟨Ccomp, hCcomp⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) A)).exists_bound_of_continuousOn
      ((by fun_prop : Continuous fun x : ℝ => x ^ n * Real.exp (-(b * x))).continuousOn)
  refine ⟨max Ccomp Ctail, fun x hx => ?_⟩
  by_cases hxA : x ≤ A
  · exact (hCcomp x ⟨hx, hxA⟩).trans (le_max_left Ccomp Ctail)
  · have hRx : R ≤ x := by
      have hRA : R ≤ A := by simp [A]
      exact hRA.trans (le_of_not_ge hxA)
    exact (hR x hRx).trans (le_max_right Ccomp Ctail)

/-- Signed moment kernels with exponential damping are integrable against finite measures on
`ℝ≥0`. -/
lemma integrable_laplaceMomentTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ := by
  obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg n ht
  refine Integrable.of_bound (C := C) (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg x.2] using hC (x : ℝ) x.2

/-- Differentiation under the integral for the signed Laplace moment kernels on `(0, ∞)`. -/
lemma hasDerivAt_laplaceMomentTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) t) t := by
  let s : Set ℝ := Metric.ball t (t / 2)
  have hs : s ∈ 𝓝 t := Metric.ball_mem_nhds t (half_pos ht)
  obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg (n + 1) (half_pos ht)
  have hF_int :
      Integrable (fun x : ℝ≥0 =>
        (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ :=
    integrable_laplaceMomentTransform μ n ht
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t) (s := s)
      (F := fun (y : ℝ) (x : ℝ≥0) =>
        (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))))
      (F' := fun (y : ℝ) (x : ℝ≥0) =>
        (-(x : ℝ)) ^ (n + 1) * Real.exp (-(y * (x : ℝ))))
      (bound := fun _ : ℝ≥0 => C)
      hs
      (by
        refine Filter.Eventually.of_forall fun y => ?_
        exact (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ)))) μ))
      hF_int
      (by
        exact (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ≥0 => (-(x : ℝ)) ^ (n + 1) *
            Real.exp (-(t * (x : ℝ)))) μ))
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        intro y hy
        have hypos : t / 2 ≤ y := by
          have hdist : dist y t < t / 2 := hy
          rw [Real.dist_eq] at hdist
          have hleft := (abs_lt.mp hdist).1
          linarith
        have hnonneg : 0 ≤ (x : ℝ) := x.2
        have hle_exp :
            Real.exp (-(y * (x : ℝ))) ≤ Real.exp (-((t / 2) * (x : ℝ))) := by
          exact Real.exp_le_exp.mpr
            (neg_le_neg (mul_le_mul_of_nonneg_right hypos hnonneg))
        have hpow_nonneg : 0 ≤ (x : ℝ) ^ (n + 1) := pow_nonneg hnonneg _
        calc
          ‖(-(x : ℝ)) ^ (n + 1) * Real.exp (-(y * (x : ℝ)))‖
              = (x : ℝ) ^ (n + 1) * Real.exp (-(y * (x : ℝ))) := by
                rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg hnonneg,
                  Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ (x : ℝ) ^ (n + 1) * Real.exp (-((t / 2) * (x : ℝ))) := by
                exact mul_le_mul_of_nonneg_left hle_exp hpow_nonneg
          _ = ‖(x : ℝ) ^ (n + 1) * Real.exp (-((t / 2) * (x : ℝ)))‖ := by
                rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hnonneg,
                  Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ C := hC (x : ℝ) x.2)
      (integrable_const C)
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        intro y _hy
        have hlin : HasDerivAt (fun y : ℝ => -(y * (x : ℝ))) (-(x : ℝ)) y := by
          have hmul : HasDerivAt (fun y : ℝ => y * (x : ℝ)) (x : ℝ) y :=
            hasDerivAt_mul_const (x : ℝ)
          exact hmul.neg
        have hder := hlin.exp.const_mul ((-(x : ℝ)) ^ n)
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hder)
  change HasDerivAt (fun y : ℝ =>
    ∫ x : ℝ≥0, (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))) ∂μ)
    (∫ x : ℝ≥0, (-(x : ℝ)) ^ (n + 1) * Real.exp (-(t * (x : ℝ))) ∂μ) t
  simpa [laplaceMomentTransform] using h.2

/-- On the open half-line, the iterated within-derivatives of a finite-measure Laplace transform
are the signed moment kernel integrals. -/
lemma iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDerivWithin n (laplaceTransform μ) (Ioi 0) t =
      laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      calc
        derivWithin (iteratedDerivWithin n (laplaceTransform μ) (Ioi 0)) (Ioi 0) t
            = derivWithin (laplaceMomentTransform μ n) (Ioi 0) t := by
              exact derivWithin_congr (fun y hy => ih hy) (ih ht)
        _ = deriv (laplaceMomentTransform μ n) t := by
              rw [derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds ht)]
        _ = laplaceMomentTransform μ (n + 1) t :=
              (hasDerivAt_laplaceMomentTransform μ n ht).deriv

/-- On the open half-line, the ordinary iterated derivatives of a finite-measure Laplace transform
are the signed moment kernel integrals. -/
lemma iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (laplaceTransform μ) t = laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hev : (fun y : ℝ => iteratedDeriv n (laplaceTransform μ) y) =ᶠ[𝓝 t]
          laplaceMomentTransform μ n :=
        eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun y hy => ih hy
      rw [Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_laplaceMomentTransform μ n ht).deriv

/-- A finite-measure Laplace transform is smooth on the open half-line. -/
lemma laplaceTransform_contDiffOn_Ioi (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceTransform μ) (Ioi 0) := by
  refine contDiffOn_of_differentiableOn_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (s := Ioi (0 : ℝ)) (f := laplaceTransform μ) ?_
  intro m _hm
  have hdiff_moment : DifferentiableOn ℝ (laplaceMomentTransform μ m) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_laplaceMomentTransform μ m ht).differentiableAt.differentiableWithinAt
  exact hdiff_moment.congr fun t ht =>
    iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform μ m ht

/-- Every finite-measure Laplace transform is completely monotone on `(0, ∞)`. -/
theorem laplaceTransform_isCompletelyMonotoneOnIoi
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    IsCompletelyMonotoneOnIoi (laplaceTransform μ) := by
  refine ⟨laplaceTransform_contDiffOn_Ioi μ, fun n t ht => ?_⟩
  rw [iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform μ n ht]
  rw [laplaceMomentTransform]
  rw [← integral_const_mul]
  refine integral_nonneg fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp : 0 ≤ Real.exp (-(t * (x : ℝ))) := Real.exp_nonneg _
  have heq : (-1 : ℝ) ^ n * ((-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) =
      (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  simpa [heq] using mul_nonneg hpow hexp

/-- The second advertised gap is discharged unconditionally. -/
theorem laplaceTransformOpenCompletelyMonotone :
    LaplaceTransformOpenCompletelyMonotone := by
  intro μ hμ
  letI := hμ
  exact laplaceTransform_isCompletelyMonotoneOnIoi μ

/-- The Laplace transform of a finite measure is completely monotone in the closed-half-line
roadmap sense. -/
theorem laplaceTransform_isClosedCompletelyMonotone
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ] :
    IsClosedCompletelyMonotone (laplaceTransform μ) :=
  ⟨laplaceTransform_continuousOn_halfLine μ, laplaceTransform_isCompletelyMonotoneOnIoi μ⟩

/-- Conditional strong easy direction: with all moments finite, the Laplace transform satisfies the
stronger existing `IsCompletelyMonotone` predicate using derivatives within `[0, ∞)`. -/
theorem laplaceTransform_isCompletelyMonotone_of_moments
    (hapi : LaplaceTransformCompletelyMonotoneOfMoments)
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    IsCompletelyMonotone (laplaceTransform μ) :=
  hapi μ hμ hmom

/-! ## Representation predicate -/

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
@[expose] def RepresentsLaplace (f : ℝ → ℝ) (μ : Measure ℝ≥0) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

namespace RepresentsLaplace

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A representing measure is finite. -/
lemma isFiniteMeasure (h : RepresentsLaplace f μ) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace-transform values on `[0, ∞)`. -/
lemma eq_laplaceTransform (h : RepresentsLaplace f μ) {t : ℝ} (ht : 0 ≤ t) :
    f t = laplaceTransform μ t :=
  h.2 t ht

end RepresentsLaplace

/-! ## Hard direction: extraction from the Chafaï measures -/

/-- Uniform tightness of the Chafaï rescaled approximating measures. -/
@[expose] def ChafaiRescaledTight (f : ℝ → ℝ) : Prop :=
  IsTightMeasureSet (Set.range (chafaiRescaled f))

private lemma chafaiRescaled_closedBall_compl_le
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (chafaiRescaled f n) (Metric.closedBall (0 : ℝ≥0) r)ᶜ ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
  let coord : ℝ≥0 → ENNReal := fun p => ENNReal.ofReal (p : ℝ)
  have hcoord_meas : AEMeasurable coord (chafaiRescaled f n) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hε0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hεtop : ENNReal.ofReal r ≠ (∞ : ENNReal) := ENNReal.ofReal_ne_top
  have hmarkov : (chafaiRescaled f n) {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} ≤
      (∫⁻ p : ℝ≥0, coord p ∂(chafaiRescaled f n)) / ENNReal.ofReal r :=
    meas_ge_le_lintegral_div hcoord_meas hε0 hεtop
  have hsubset :
      (Metric.closedBall (0 : ℝ≥0) r)ᶜ ⊆ {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} := by
    intro p hp
    have hpdist : r < dist p (0 : ℝ≥0) := by
      simpa [Metric.mem_closedBall, not_le] using hp
    have hdist : dist p (0 : ℝ≥0) = (p : ℝ) := by
      simp [NNReal.dist_eq]
    have hle : r ≤ (p : ℝ) := by linarith
    exact ENNReal.ofReal_le_ofReal hle
  calc
    (chafaiRescaled f n) (Metric.closedBall (0 : ℝ≥0) r)ᶜ
        ≤ (chafaiRescaled f n) {p : ℝ≥0 | ENNReal.ofReal r ≤ coord p} :=
          measure_mono hsubset
    _ ≤ (∫⁻ p : ℝ≥0, coord p ∂(chafaiRescaled f n)) / ENNReal.ofReal r := hmarkov
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / ENNReal.ofReal r :=
          ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _
    _ = ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
          rw [ENNReal.ofReal_div_of_pos hr]

/-- Completely monotone functions give a tight family of rescaled Chafaï measures.

The proof uses the Chafaï first-moment bound from `BernsteinMeasures` and Markov's inequality.
Since the measure space is `ℝ≥0` rather than a normed additive group, it applies Mathlib's
closed-ball tightness criterion. -/
theorem chafaiRescaledTight {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f) :
    ChafaiRescaledTight f := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall
    (S := Set.range (chafaiRescaled f)) (x := (0 : ℝ≥0)) ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hreal : Tendsto (fun r : ℝ => -derivWithin f (Ici 0) 0 / r) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop tendsto_id _
  have henn : Tendsto (fun r : ℝ => ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r))
      atTop (nhds (0 : ENNReal)) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hsmall := (ENNReal.tendsto_nhds_zero.mp henn) ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with r hr hsmallr
  have hbound :
      (⨆ μ ∈ Set.range (chafaiRescaled f), μ (Metric.closedBall (0 : ℝ≥0) r)ᶜ) ≤
        ENNReal.ofReal (-derivWithin f (Ici 0) 0 / r) := by
    rw [iSup₂_le_iff]
    intro μ hμ
    rcases hμ with ⟨n, rfl⟩
    exact chafaiRescaled_closedBall_compl_le hcm hr n
  exact hbound.trans hsmallr

/-- Gap statement: the Chafaï rescaled measures have Laplace integrals converging back to `f`.

This is the analytic identification step before passing to a Prokhorov weak limit.

Missing argument: identify the rescaled kernel integrals with the Chafaï/Taylor remainder
expressions and prove their limit is `f t`; the existing weak-convergence specialization only
identifies the Laplace integrals of an already extracted weak cluster point.

This over-strong formulation is not used below: for a completely monotone function with
`f(t) → L`, the Chafaï densities represent the nonconstant part, so the rescaled integrals can
only converge to `f t - L` in general. The representing measure must then add the missing atom
`L δ₀`. -/
@[expose] def ChafaiRescaledLaplaceConvergence (f : ℝ → ℝ) : Prop :=
  ∀ {l : Filter ℕ}, l ≤ atTop → ∀ {t : ℝ}, 0 ≤ t →
    Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) l
      (nhds (f t))

/-- Residual analytic Chafaï convergence in its correct nonconstant-part form.

If `f(t) → L` at infinity, the Chafaï densities have total mass `f 0 - L`; their Laplace
integrals should converge to `f t - L`. The extraction proof below adds the missing atom
`L δ₀`, whose Laplace transform is the constant `L`. -/
@[expose] def ChafaiRescaledLaplaceConvergenceToNonconstantPart (f : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
    ∀ {l : Filter ℕ}, l ≤ atTop → ∀ {t : ℝ}, 0 ≤ t →
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) l
        (nhds (f t - L))

/-- Existence of a finite representing measure for a function satisfying the existing strong
`IsCompletelyMonotone` predicate.

This is the part of the hard direction that the Part-1 Chafaï infrastructure is designed to feed:
use the mass bound, prove tightness, extract a weak cluster point, and identify the Laplace
integrals of the limit. -/
theorem exists_laplaceTransform_of_isCompletelyMonotone_of_chafai
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f)
    (hconv : ChafaiRescaledLaplaceConvergenceToNonconstantPart f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  obtain ⟨L, _hL, hL_nonneg, hconv⟩ := hconv
  obtain ⟨_L, C, _hL, _hL_nonneg, _hC, hmass⟩ :=
    chafaiRescaled_prokhorov_mass_bound f hcm
  obtain ⟨μ, U, hUle, hμ_fin, _hμ_mass, hweak⟩ :=
    finite_measure_cluster_limit (σ := chafaiRescaled f) C
      (fun n => (hmass n).2) (chafaiRescaledTight hcm)
  let ν : Measure ℝ≥0 := μ + ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)
  have hatom_fin : IsFiniteMeasure (ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)) := by
    refine ⟨?_⟩
    simp
  letI := hatom_fin
  have hν_fin : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  refine ⟨ν, hν_fin, fun t ht => ?_⟩
  letI := hν_fin
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ)
        (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak
      (μ₀ := μ) (l := (U : Filter ℕ)) hweak ht
  have hchafai :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ) (nhds (f t - L)) :=
    hconv hUle ht
  have hμ_laplace :
      f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ :=
    tendsto_nhds_unique hchafai hweak_laplace
  have hν_laplace :
      laplaceTransform ν t = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by
    have hμ_int : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ :=
      integrable_laplaceKernel_of_nonneg μ ht
    have hatom_int : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
        (ENNReal.ofReal L • Measure.dirac (0 : ℝ≥0)) := by
      letI := hatom_fin
      exact integrable_laplaceKernel_of_nonneg _ ht
    calc
      laplaceTransform ν t
          = ∫ p, Real.exp (-(t * (p : ℝ))) ∂ν := rfl
      _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) +
            ∫ p, Real.exp (-(t * (p : ℝ))) ∂(ENNReal.ofReal L •
              Measure.dirac (0 : ℝ≥0)) := by
            dsimp [ν]
            rw [integral_add_measure hμ_int hatom_int]
      _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by
            rw [integral_smul_measure, integral_dirac]
            simp [hL_nonneg]
  calc
    f t = (f t - L) + L := by ring
    _ = (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ) + L := by rw [hμ_laplace]
    _ = laplaceTransform ν t := hν_laplace.symm

/-! ## Uniqueness -/

/-- Gap statement: Laplace transforms are injective on finite measures on `ℝ≥0`.

Missing argument: uniqueness of finite measures from their Laplace transforms, e.g. via
Stone-Weierstrass density of the algebra generated by `x ↦ exp (-(t * x))`, or a finite-measure
Laplace uniqueness theorem in Mathlib. -/
@[expose] def LaplaceTransformInjectiveOnFiniteMeasures : Prop :=
  ∀ {μ ν : Measure ℝ≥0}, IsFiniteMeasure μ → IsFiniteMeasure ν →
    (∀ t : ℝ, 0 ≤ t → laplaceTransform μ t = laplaceTransform ν t) → μ = ν

/-- Conditional uniqueness: if finite-measure Laplace transforms are injective, a function has at
most one finite representing measure. -/
theorem laplaceTransform_unique
    (hinj : LaplaceTransformInjectiveOnFiniteMeasures)
    {f : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hμ : RepresentsLaplace f μ) (hν : RepresentsLaplace f ν) :
    μ = ν :=
  hinj hμ.isFiniteMeasure hν.isFiniteMeasure fun t ht => by
    rw [← hμ.eq_laplaceTransform ht, ← hν.eq_laplaceTransform ht]

/-! ## Headline theorem -/

/-- Statement of the **Hausdorff--Bernstein--Widder theorem**, finite-measure version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is the
Laplace transform of a finite positive measure on `ℝ≥0`, on the nonnegative half-line. -/
@[expose] def BernsteinTheorem : Prop :=
  ∀ f : ℝ → ℝ,
    IsClosedCompletelyMonotone f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ

/-- Unique-existence statement of the Hausdorff--Bernstein--Widder theorem. -/
@[expose] def BernsteinUniqueTheorem : Prop :=
  ∀ f : ℝ → ℝ,
    IsClosedCompletelyMonotone f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ

/-- Assemble the non-unique Bernstein theorem from separately supplied existence and easy
directions. -/
theorem bernstein_of_exists_of_laplaceTransform
    (hexists :
      ∀ f : ℝ → ℝ, IsClosedCompletelyMonotone f →
        ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ)
    (hlaplace :
      ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
        IsClosedCompletelyMonotone (laplaceTransform μ)) :
    BernsteinTheorem := by
  intro f
  constructor
  · exact hexists f
  · rintro ⟨μ, hμ⟩
    exact (hlaplace μ hμ.isFiniteMeasure).congr fun t ht =>
      hμ.eq_laplaceTransform ht

/-- Assemble the unique-existence Bernstein theorem from the non-unique theorem and injectivity of
finite-measure Laplace transforms. -/
theorem bernstein_unique_of_bernstein_of_injective
    (hbernstein : BernsteinTheorem)
    (hinj : LaplaceTransformInjectiveOnFiniteMeasures) :
    BernsteinUniqueTheorem := by
  intro f
  constructor
  · intro hf
    obtain ⟨μ, hμ⟩ := (hbernstein f).mp hf
    exact ⟨μ, hμ, fun ν hν =>
      (laplaceTransform_unique (f := f) (μ := μ) (ν := ν) hinj hμ hν).symm⟩
  · rintro ⟨μ, hμ, _huniq⟩
    exact (hbernstein f).mpr ⟨μ, hμ⟩

/-- Strong-predicate unique-existence corollary, conditional on Chafaï Laplace convergence and
Laplace injectivity. -/
theorem bernstein_unique_of_isCompletelyMonotone_of_chafai
    (hinj : LaplaceTransformInjectiveOnFiniteMeasures)
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f)
    (hconv : ChafaiRescaledLaplaceConvergenceToNonconstantPart f) :
    ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  obtain ⟨μ, hμ⟩ :=
    exists_laplaceTransform_of_isCompletelyMonotone_of_chafai hcm hconv
  exact ⟨μ, hμ, fun ν hν =>
    (laplaceTransform_unique (f := f) (μ := μ) (ν := ν) hinj hμ hν).symm⟩

end TauCeti
