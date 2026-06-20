/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The metric of a compatible pair

A symplectic form `ω` compatible with an almost complex structure `J` determines a Riemannian
metric `g(v, w) = ω(v, J w)`. This file records the standard compatible-triple identities tying
`ω`, `J`, and `g` together, and packages the metric of a compatible pair as a genuine inner
product through Mathlib's `InnerProductSpace.Core`.

The metric is `TauCeti.SymplecticForm.associatedBilinForm`, already defined in
`AlmostComplex.lean`. Compatibility makes it symmetric and positive definite (recorded there);
here we add the relations that turn `(ω, J, g)` into a compatible triple: `J` is a `g`-isometry,
`J` is `g`-skew-adjoint, and `ω` is recovered from `g` and `J`. The capstone
`TauCeti.SymplecticForm.Compatible.innerProductCore` exhibits `g` as an inner product, the
witness that the pointwise compatibility definition is non-vacuous and behaves as a metric
should; the energy of a `J`-holomorphic curve in the analytic Heegaard Floer roadmap is measured
against exactly this metric.

## Main declarations

* `TauCeti.SymplecticForm.associatedBilinForm_apply_right_apply`: `g(v, J w) = -ω(v, w)`, holding
  for any `J` from the identity `J² = -1` alone.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_apply_left_apply`: `g(J v, w) = ω(v, w)`,
  recovering `ω` from the metric.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_invariant`: `J` is a `g`-isometry,
  `g(J v, J w) = g(v, w)`.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_skewAdjoint`: `J` is `g`-skew-adjoint,
  `g(J v, w) = -g(v, J w)`.
* `TauCeti.SymplecticForm.Compatible.associatedBilinForm_nondegenerate`: the metric is
  nondegenerate.
* `TauCeti.SymplecticForm.Compatible.innerProductCore`: the metric of a compatible pair as an
  `InnerProductSpace.Core ℝ V`.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: a compatible pair `(ω, J)` determines a metric `g(v, w) = ω(v, J w)`.
-/

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- Applying `J` to the right argument of the metric `g(v, w) = ω(v, J w)` negates the symplectic
form: `g(v, J w) = -ω(v, w)`. This uses only `J² = -1`, not compatibility. -/
@[simp]
lemma associatedBilinForm_apply_right_apply (v w : V) :
    ω.associatedBilinForm J v (J w) = -ω v w := by
  rw [associatedBilinForm_apply, AlmostComplexStructure.apply_apply]
  exact map_neg (ω.toBilinForm v) w

namespace Compatible

/-- The metric recovers the symplectic form: `g(J v, w) = ω(v, w)`. -/
lemma associatedBilinForm_apply_left_apply (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) w = ω v w := by
  rw [associatedBilinForm_apply, h.invariant_apply]

/-- The symplectic form is recovered from the metric and `J`: `ω(v, w) = g(J v, w)`. -/
lemma symplecticForm_eq_associatedBilinForm (h : ω.Compatible J) (v w : V) :
    ω v w = ω.associatedBilinForm J (J v) w :=
  (h.associatedBilinForm_apply_left_apply v w).symm

/-- `J` is an isometry of the metric `g`: `g(J v, J w) = g(v, w)`. -/
lemma associatedBilinForm_invariant (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) (J w) = ω.associatedBilinForm J v w := by
  rw [h.associatedBilinForm_apply_left_apply v (J w), associatedBilinForm_apply]

/-- `J` is skew-adjoint for the metric `g`: `g(J v, w) = -g(v, J w)`. -/
lemma associatedBilinForm_skewAdjoint (h : ω.Compatible J) (v w : V) :
    ω.associatedBilinForm J (J v) w = -ω.associatedBilinForm J v (J w) := by
  rw [h.associatedBilinForm_apply_left_apply, associatedBilinForm_apply_right_apply, neg_neg]

/-- The metric `g(v, v) = ω(v, J v)` is nonnegative. -/
lemma associatedBilinForm_self_nonneg (h : ω.Compatible J) (v : V) :
    0 ≤ ω.associatedBilinForm J v v := by
  simpa [LinearMap.BilinMap.toQuadraticMap_apply] using h.positive.nonneg v

/-- The diagonal of the metric `v ↦ ω(v, J v)` is nonnegative. -/
lemma symplecticForm_apply_self_nonneg (h : ω.Compatible J) (v : V) : 0 ≤ ω v (J v) :=
  h.associatedBilinForm_self_nonneg v

/-- The metric is positive definite in the sense that `g(v, v) = 0` exactly when `v = 0`. -/
lemma associatedBilinForm_self_eq_zero (h : ω.Compatible J) {v : V} :
    ω.associatedBilinForm J v v = 0 ↔ v = 0 := by
  refine ⟨fun hv => h.positive.anisotropic v ?_, ?_⟩
  · simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hv
  · rintro rfl
    simp

/-- The metric of a compatible pair is nondegenerate. -/
lemma associatedBilinForm_nondegenerate (h : ω.Compatible J) :
    (ω.associatedBilinForm J).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    h.associatedBilinForm_isSymm.isRefl).mpr ?_
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  intro v hv
  refine h.associatedBilinForm_self_eq_zero.mp ?_
  simpa using LinearMap.congr_fun hv v

/-- The metric of a compatible pair, packaged as an `InnerProductSpace.Core ℝ V`.

The inner product is `⟪v, w⟫ = ω(v, J w)`: compatibility makes it symmetric (`conj_inner_symm`),
nonnegative on the diagonal (`re_inner_nonneg`), and positive definite (`definite`), while
bilinearity of `ω` supplies additivity and homogeneity in the first slot. This is the witness
that the pointwise compatibility definition really yields a Euclidean inner product. -/
@[reducible]
noncomputable def innerProductCore (h : ω.Compatible J) : InnerProductSpace.Core ℝ V where
  inner v w := ω v (J w)
  conj_inner_symm v w := by
    change (starRingEnd ℝ) (ω w (J v)) = ω v (J w)
    rw [RCLike.conj_to_real, h.associatedBilinForm_apply_swap w v]
  re_inner_nonneg v := by
    simpa using h.symplecticForm_apply_self_nonneg v
  add_left v w x := by
    change ω.toBilinForm (v + w) (J x) = ω.toBilinForm v (J x) + ω.toBilinForm w (J x)
    rw [map_add, LinearMap.add_apply]
  smul_left v w r := by
    change ω.toBilinForm (r • v) (J w) = (starRingEnd ℝ) r * ω.toBilinForm v (J w)
    rw [RCLike.conj_to_real, map_smul, LinearMap.smul_apply, smul_eq_mul]
  definite v hv := h.associatedBilinForm_self_eq_zero.mp hv

@[simp]
lemma innerProductCore_inner (h : ω.Compatible J) (v w : V) :
    @inner ℝ V h.innerProductCore.toInner v w = ω v (J w) :=
  rfl

end Compatible

end SymplecticForm

end TauCeti
