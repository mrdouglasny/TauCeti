/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Equiv.Basic
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Transporting almost complex structures along linear equivalences

A real-linear isomorphism `e : V ≃ₗ[ℝ] W` carries an almost complex structure `J` on `V` to
one on `W` by conjugation, `w ↦ e (J (e.symm w))`. This file records that transport and its
functoriality, and packages the statement that `e` itself is then a complex-linear isomorphism
between `(V, J)` and `(W, J.transport e)`.

This is the pointwise naturality that the smooth layer of the analytic Heegaard Floer roadmap
needs: an almost complex structure on a vector bundle is given fiberwise, and a change of
trivialization acts on each fiber by exactly this conjugation. The capstone
`IsComplexLinearMap.arrowCongr` says that complex-linearity of a map is preserved when both
source and target are transported, so the whole `J`-holomorphic dictionary moves along
isomorphisms without being restated.

## Main declarations

* `TauCeti.AlmostComplexStructure.transport`: the almost complex structure `e.conj J` on `W`,
  obtained by conjugating `J` with `e : V ≃ₗ[ℝ] W`.
* `TauCeti.AlmostComplexStructure.transport_refl` / `transport_trans`: functoriality of
  transport in the linear equivalence.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_transport`: the equivalence `e` is
  complex-linear from `J` to `J.transport e`.
* `TauCeti.IsComplexLinearMap.arrowCongr`: complex-linearity transports along a pair of linear
  equivalences applied to the source and target.

The conjugation `LinearEquiv.conj` and `LinearEquiv.arrowCongr` are reused from Mathlib; the
almost complex structure layer is `TauCeti.AlmostComplexStructure`.
-/

namespace TauCeti

variable {V W X : Type*}

namespace AlmostComplexStructure

variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup X] [Module ℝ X]

/-- The underlying linear map determines an almost complex structure: the only data is the
endomorphism, the defining identity being a proposition. -/
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : AlmostComplexStructure V → (V →ₗ[ℝ] V)) := by
  rintro ⟨L, hL⟩ ⟨L', hL'⟩ h
  subst h
  rfl

/-- Transport an almost complex structure along a real-linear equivalence by conjugation.

The endomorphism is `LinearEquiv.conj e` applied to `J`, that is `w ↦ e (J (e.symm w))`; it
again squares to `-1` because conjugation is multiplicative and fixes `±id`. -/
def transport (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) : AlmostComplexStructure W where
  toLinearMap := e.conj J.toLinearMap
  square_neg := by
    rw [← LinearEquiv.conj_comp, J.square_neg, map_neg, LinearEquiv.conj_id]

@[simp]
lemma transport_toLinearMap (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) :
    (J.transport e).toLinearMap = e.conj J.toLinearMap := rfl

@[simp]
lemma transport_apply (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) (w : W) :
    J.transport e w = e (J (e.symm w)) := rfl

/-- Transporting along the identity equivalence does nothing. -/
@[simp]
lemma transport_refl (J : AlmostComplexStructure V) :
    J.transport (LinearEquiv.refl ℝ V) = J :=
  toLinearMap_injective (by ext v; simp)

/-- Transport is functorial: transporting along `e₁` then `e₂` is transporting along their
composite. -/
lemma transport_trans (J : AlmostComplexStructure V) (e₁ : V ≃ₗ[ℝ] W) (e₂ : W ≃ₗ[ℝ] X) :
    (J.transport e₁).transport e₂ = J.transport (e₁ ≪≫ₗ e₂) := by
  apply toLinearMap_injective
  simp only [transport_toLinearMap]
  rw [← LinearEquiv.trans_apply, LinearEquiv.conj_trans]

/-- Transporting forward along `e` and back along `e.symm` returns the original structure. -/
@[simp]
lemma transport_symm_transport (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) :
    (J.transport e).transport e.symm = J := by
  rw [transport_trans, e.self_trans_symm, transport_refl]

/-- Transporting back along `e.symm` and forward along `e` returns the original structure. -/
@[simp]
lemma transport_transport_symm (J : AlmostComplexStructure W) (e : V ≃ₗ[ℝ] W) :
    (J.transport e.symm).transport e = J := by
  rw [transport_trans, e.symm_trans_self, transport_refl]

/-- Transport commutes with negation of the almost complex structure. -/
@[simp]
lemma transport_neg (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) :
    (-J).transport e = -(J.transport e) := by
  apply toLinearMap_injective
  simp only [transport_toLinearMap, neg_toLinearMap, map_neg]

/-- A linear equivalence is complex-linear from `J` to its transport `J.transport e`. -/
lemma isComplexLinearMap_transport (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) :
    IsComplexLinearMap J (J.transport e) e.toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp

/-- The inverse equivalence is complex-linear from `J.transport e` back to `J`. -/
lemma isComplexLinearMap_symm_transport (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] W) :
    IsComplexLinearMap (J.transport e) J e.symm.toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro w
  simp

end AlmostComplexStructure

section Naturality

variable {V₁ V₂ W₁ W₂ : Type*}
variable [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
variable [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]

/-- Complex-linearity transports along a pair of linear equivalences: if `F` intertwines `J`
and `J'`, then conjugating `F` by `eV` on the source and `eW` on the target intertwines the
transported structures. -/
lemma IsComplexLinearMap.arrowCongr {J : AlmostComplexStructure V₁}
    {J' : AlmostComplexStructure W₁} {F : V₁ →ₗ[ℝ] W₁} (hF : IsComplexLinearMap J J' F)
    (eV : V₁ ≃ₗ[ℝ] V₂) (eW : W₁ ≃ₗ[ℝ] W₂) :
    IsComplexLinearMap (J.transport eV) (J'.transport eW) (eV.arrowCongr eW F) := by
  rw [isComplexLinearMap_iff_apply] at hF ⊢
  intro v
  simp only [LinearEquiv.arrowCongr_apply, AlmostComplexStructure.transport_apply,
    LinearEquiv.symm_apply_apply]
  rw [hF]

end Naturality

end TauCeti
