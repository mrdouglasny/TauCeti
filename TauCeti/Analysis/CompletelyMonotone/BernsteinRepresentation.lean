/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.CompletelyMonotone.BernsteinChafaiIdentity
public import TauCeti.Analysis.CompletelyMonotone.Limits
public import TauCeti.Analysis.CompletelyMonotone.BernsteinKernelConv

/-!
# Bernstein's representation theorem (forward direction)

Bernstein's theorem represents a completely monotone function as the Laplace transform of a
positive measure on `[0, ∞)`. This file assembles the **forward direction** for
`TauCeti.IsCompletelyMonotone`, the closed-half-line notion from
`TauCeti.Analysis.CompletelyMonotone.Basic`: every completely monotone `f` is the Laplace
transform of a finite measure on `ℝ≥0` (`IsCompletelyMonotone.exists_measure`).

The Chafaï construction lives in the supporting files (`BernsteinAux`, `BernsteinMeasures`,
`BernsteinChafaiIdentity`, `BernsteinProkhorov`, `BernsteinKernelConv`); here we tie the pieces
together directly on `Measure ℝ≥0`, the TauCeti convention for Bernstein representing measures.

This implements the Bernstein theorem milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B.

## Scope and the finite-vs-all-moments subtlety

We state only the forward existence here, with a **finite** representing measure — exactly what
complete monotonicity on the closed half-line yields. The *biconditional* is deferred (PR #2):
the converse "finite measure ⟹ completely monotone" is **false** for this closed-half-line
class — e.g. `t ↦ ∫₀^∞ e^{-x t}(1+x)⁻² dx` comes from a finite measure yet has `f'(0⁺) = -∞`,
so it is not `C^∞` at `0`. The class that closed complete monotonicity matches biconditionally
is the measures with **all moments finite**. See the `TODO` block at the end.

## Main declarations

* `TauCeti.laplaceTransformMeasure`: `t ↦ ∫ e^{-t x} dμ`, the Laplace transform of a measure
  on `ℝ≥0`.
* `TauCeti.IsCompletelyMonotone.exists_measure`: every completely monotone function on
  `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- The **Laplace transform** of a measure `μ` on `ℝ≥0`, evaluated at `t : ℝ`:
`t ↦ ∫ e^{-t x} dμ(x)`. By Bernstein's theorem every completely monotone function on
`[0, ∞)` is of this form for a finite `μ` (`IsCompletelyMonotone.exists_measure`). -/
noncomputable def laplaceTransformMeasure (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * (x : ℝ)) ∂μ

/-- For a completely monotone `f`, there is a limit `L ≥ 0` and a finite measure `μ₀` on `ℝ≥0`
with `f t = L + ∫ e^{-tp} dμ₀`. -/
private lemma cm_laplace_representation (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ μ₀ : Measure ℝ≥0, IsFiniteMeasure μ₀ ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
  obtain ⟨L, hL, hL_nn, hmass⟩ := chafaiMeasure_finite_mass f hcm
  have hfin_rescaled : ∀ n, 2 ≤ n → IsFiniteMeasure (chafaiRescaled f n) := by
    intro n hn
    haveI := (hmass n).1
    exact chafaiRescaled_isFiniteMeasure f n
  have hmass_rescaled : ∀ n, 2 ≤ n →
      (chafaiRescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
    intro n hn
    rw [chafaiRescaled_mass_eq]
    exact (hmass n).2
  have hchafai : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p : ℝ≥0, bernstein_kernel n x (p : ℝ) ∂(chafaiRescaled f n) :=
    fun n hn x hx => chafai_identity f hcm n hn x hx L hL
  obtain ⟨μ₀, hfin₀, hrep⟩ :=
    prokhorov_limit_identification f hcm L hL hL_nn hmass_rescaled hfin_rescaled hchafai
  exact ⟨L, hL_nn, μ₀, hfin₀, hrep⟩

/-- **Packaging step**: if `f(x) = L + ∫ e^{-xp} dμ₀`, then `μ = μ₀ + L·δ₀` gives
`f(x) = ∫ e^{-xp} dμ` with `μ` finite. -/
private lemma exists_integral_exp_neg_mul_of_const_add {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    {μ₀ : Measure ℝ≥0} [IsFiniteMeasure μ₀]
    (hrep : ∀ t, 0 ≤ t → f t = L + ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t, 0 ≤ t → f t = ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ := by
  set μ := μ₀ + (ENNReal.ofReal L) • Measure.dirac (0 : ℝ≥0)
  haveI : IsFiniteMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.ofReal_lt_top⟩
  refine ⟨μ, inferInstance, fun t ht => ?_⟩
  rw [hrep t ht]
  set ν := (ENNReal.ofReal L) • Measure.dirac (0 : ℝ≥0)
  have exp_int : ∀ (μ' : Measure ℝ≥0) [IsFiniteMeasure μ'],
      Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ' := by
      intro μ' _
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · fun_prop
      · apply ae_of_all
        intro p
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht p.2))
  have h1 : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ₀ := exp_int μ₀
  have h2 : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) ν := by
    haveI : IsFiniteMeasure ν := by
      constructor
      simp only [ν, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
      exact ENNReal.ofReal_lt_top
    exact exp_int ν
  change L + ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ₀ =
    ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂(μ₀ + ν)
  rw [integral_add_measure h1 h2]
  suffices h : ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂ν = L by linarith
  rw [@integral_smul_measure ℝ≥0 ℝ _ _ _ (Measure.dirac (0 : ℝ≥0))
    (fun p => Real.exp (-(t * (p : ℝ)))) (ENNReal.ofReal L),
    integral_dirac, ENNReal.toReal_ofReal hL,
    NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, mul_one]

/-- **Bernstein's theorem** on `Measure ℝ≥0`: every completely monotone `f` on `[0, ∞)` is the
Laplace transform of a finite measure. -/
private lemma bernstein_theorem_nnreal (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = ∫ p : ℝ≥0, Real.exp (-(t * (p : ℝ))) ∂μ := by
  obtain ⟨L, hL_nonneg, μ₀, hfin₀, hrep⟩ := cm_laplace_representation hcm
  exact exists_integral_exp_neg_mul_of_const_add hL_nonneg hrep

/-- **Bernstein's theorem, forward direction.** Every completely monotone function on the
closed half-line `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

The representing measure is built directly on `ℝ≥0`; nonnegative support is carried by the type. -/
theorem IsCompletelyMonotone.exists_measure (hf : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
  obtain ⟨μ, hfin, hrep⟩ := bernstein_theorem_nnreal hf
  exact ⟨μ, hfin, fun t ht => by simpa [laplaceTransformMeasure] using hrep t ht⟩

-- TODO (PR #2 — the biconditional, all-moments form). The textbook iff requires the
-- *all-moments* condition on the measure side, not mere finiteness (see the scope note above):
--   def HasAllMoments (μ : Measure ℝ≥0) : Prop := ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x:ℝ)^n) μ
--   theorem isCompletelyMonotone_laplaceTransformMeasure (hμ : HasAllMoments μ) :
--       IsCompletelyMonotone (laplaceTransformMeasure μ)              -- ⇐, differentiate under ∫
--   theorem laplaceTransformMeasure_injective ...                    -- uniqueness
--   theorem bernstein (f : ℝ → ℝ) :
--     IsCompletelyMonotone f ↔
--       ∃! μ : Measure ℝ≥0, HasAllMoments μ ∧ ∀ t ≥ 0, f t = laplaceTransformMeasure μ t

end TauCeti
