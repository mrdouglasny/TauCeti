/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
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

/-- Gap statement: every finite-measure Laplace transform is continuous on `[0, ∞)`.

Missing argument: dominated convergence for the parameter integral, dominated by the constant
`1` on the half-line `0 ≤ t`. -/
@[expose] def LaplaceTransformContinuousOnHalfLine : Prop :=
  ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ → ContinuousOn (laplaceTransform μ) (Ici 0)

/-- Gap statement: every finite-measure Laplace transform is completely monotone on `(0, ∞)`.

Missing argument: dominated differentiation under the integral for
`t ↦ exp (-(t * x))`, with local domination by bounded multiples of
`x ^ n * exp (-(a * x))`. -/
@[expose] def LaplaceTransformOpenCompletelyMonotone : Prop :=
  ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
    IsCompletelyMonotoneOnIoi (laplaceTransform μ)

/-- Gap statement: finite measures with all moments finite satisfy the stronger existing
`IsCompletelyMonotone` predicate for their Laplace transforms.

Missing argument: closed-half-line differentiation under the integral with moment domination at
`0`. -/
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

/-- Conditional easy direction: once the continuity and open-half-line differentiation gap
statements are supplied, the Laplace transform of a finite measure is completely monotone in the
closed-half-line roadmap sense. -/
theorem laplaceTransform_isClosedCompletelyMonotone
    (hcont : LaplaceTransformContinuousOnHalfLine)
    (hopen : LaplaceTransformOpenCompletelyMonotone)
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ] :
    IsClosedCompletelyMonotone (laplaceTransform μ) :=
  ⟨hcont μ hμ, hopen μ hμ⟩

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

/-- Gap statement: uniform tightness of the Chafaï rescaled approximating measures.

Part 1 supplies a uniform mass bound. Prokhorov extraction additionally needs this tail estimate on
`ℝ≥0`.

Missing argument: the Chafaï tail estimate proving
`lim_R sup_n (chafaiRescaled f n) {p | R < p} = 0`, usable with
`isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt`. -/
@[expose] def ChafaiRescaledTight (f : ℝ → ℝ) : Prop :=
  IsTightMeasureSet (Set.range (chafaiRescaled f))

/-- Gap statement: the Chafaï rescaled measures have Laplace integrals converging back to `f`.

This is the analytic identification step before passing to a Prokhorov weak limit.

Missing argument: identify the rescaled kernel integrals with the Chafaï/Taylor remainder
expressions and prove their limit is `f t`. -/
@[expose] def ChafaiRescaledLaplaceConvergence (f : ℝ → ℝ) : Prop :=
  ∀ {l : Filter ℕ}, l ≤ atTop → ∀ {t : ℝ}, 0 ≤ t →
    Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) l
      (nhds (f t))

/-- Existence of a finite representing measure for a function satisfying the existing strong
`IsCompletelyMonotone` predicate.

This is the part of the hard direction that the Part-1 Chafaï infrastructure is designed to feed:
use the mass bound, prove tightness, extract a weak cluster point, and identify the Laplace
integrals of the limit. -/
theorem exists_laplaceTransform_of_isCompletelyMonotone_of_chafai
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f)
    (htight : ChafaiRescaledTight f)
    (hconv : ChafaiRescaledLaplaceConvergence f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  obtain ⟨_L, C, _hL, _hL_nonneg, _hC, hmass⟩ :=
    chafaiRescaled_prokhorov_mass_bound f hcm
  obtain ⟨μ, U, hUle, hμ_fin, _hμ_mass, hweak⟩ :=
    finite_measure_cluster_limit (σ := chafaiRescaled f) C
      (fun n => (hmass n).2) htight
  refine ⟨μ, hμ_fin, fun t ht => ?_⟩
  have hweak_laplace :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ)
        (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ)) :=
    chafaiRescaled_tendsto_laplace_integral_of_weak
      (μ₀ := μ) (l := (U : Filter ℕ)) hweak ht
  have hchafai :
      Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ) (nhds (f t)) :=
    hconv hUle ht
  simpa [laplaceTransform] using tendsto_nhds_unique hchafai hweak_laplace

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

/-- Strong-predicate unique-existence corollary, conditional on the remaining Chafaï and
Laplace-injectivity gaps. -/
theorem bernstein_unique_of_isCompletelyMonotone_of_chafai
    (hinj : LaplaceTransformInjectiveOnFiniteMeasures)
    {f : ℝ → ℝ} (hcm : IsCompletelyMonotone f)
    (htight : ChafaiRescaledTight f)
    (hconv : ChafaiRescaledLaplaceConvergence f) :
    ∃! μ : Measure ℝ≥0, RepresentsLaplace f μ := by
  obtain ⟨μ, hμ⟩ :=
    exists_laplaceTransform_of_isCompletelyMonotone_of_chafai hcm htight hconv
  exact ⟨μ, hμ, fun ν hν =>
    (laplaceTransform_unique (f := f) (μ := μ) (ν := ν) hinj hμ hν).symm⟩

end TauCeti
