/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Lattice

/-!
# Inverse images of subcomodules

This file adds inverse images of subcomodules under comodule morphisms. If
`f : M → N` is a morphism of right comodules and `B ≤ N` is a subcomodule, then
`B.comap f` has underlying submodule `B.toSubmodule.comap f`. Stability under the
coaction follows by applying tensor-product right exactness to the quotient map
`N → N / B`.

This is Layer 1 infrastructure for the reductive-groups roadmap target on comodules:
subobjects of representations need both images and inverse images before kernels,
finite-subcomodule constructions, and the representation/comodule dictionary can be used
comfortably.

## Main declarations

* `TauCeti.Subcomodule.comap`: inverse image of a subcomodule under a comodule morphism.
* `TauCeti.Subcomodule.mem_comap`, `comap_toSubmodule`: characteristic API.
* `TauCeti.Subcomodule.map_le_iff_le_comap`: the usual image/preimage Galois connection.

## References

The construction is the standard inverse image of a subcomodule. The exactness step reuses
Mathlib's `TensorProduct.rTensor_exact` and `LinearMap.exact_subtype_ker_map`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x y

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommRing R]
variable [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommGroup M] [Module R M] [Comodule R C M]
variable [AddCommGroup N] [Module R N] [Comodule R C N]

namespace Subcomodule

private theorem ker_rangeRestrict_mkQ_comp (B : Submodule R N) (f : M →ₗ[R] N) :
    LinearMap.ker (B.mkQ.comp f).rangeRestrict = B.comap f := by
  ext m
  simp [LinearMap.mem_ker, Submodule.mem_comap]

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem rTensor_rangeRestrict_eq_zero_of_rTensor_eq_zero
    {B : Submodule R N} {f : M →ₗ[R] N} {t : M ⊗[R] C}
    (h : LinearMap.rTensor C (B.mkQ.comp f) t = 0) :
    LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict t = 0 := by
  apply Module.Flat.rTensor_preserves_injective_linearMap
    (LinearMap.range (B.mkQ.comp f)).subtype Subtype.val_injective
  calc
    LinearMap.rTensor C (LinearMap.range (B.mkQ.comp f)).subtype
        (LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict t)
      = (LinearMap.rTensor C (LinearMap.range (B.mkQ.comp f)).subtype ∘ₗ
          LinearMap.rTensor C (B.mkQ.comp f).rangeRestrict) t := rfl
    _ = LinearMap.rTensor C
          ((LinearMap.range (B.mkQ.comp f)).subtype.comp (B.mkQ.comp f).rangeRestrict) t := by
          rw [← LinearMap.rTensor_comp]
    _ = LinearMap.rTensor C (B.mkQ.comp f) t := by
          rfl
    _ = 0 := h

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] in
private theorem tensor_mem_range_comap (B : Submodule R N) (f : M →ₗ[R] N)
    {t : M ⊗[R] C} (h : LinearMap.rTensor C (B.mkQ.comp f) t = 0) :
    t ∈ LinearMap.range
      (TensorProduct.map (B.comap f).subtype (LinearMap.id : C →ₗ[R] C)) := by
  let g : M →ₗ[R] LinearMap.range (B.mkQ.comp f) := (B.mkQ.comp f).rangeRestrict
  have hker : LinearMap.ker g = B.comap f :=
    ker_rangeRestrict_mkQ_comp (M := M) B f
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    exact LinearMap.range_rangeRestrict (B.mkQ.comp f)
  have hexact : Function.Exact (LinearMap.ker g).subtype g :=
    LinearMap.exact_subtype_ker_map g
  have ht : t ∈ LinearMap.ker (LinearMap.rTensor C g) := by
    rw [LinearMap.mem_ker]
    exact rTensor_rangeRestrict_eq_zero_of_rTensor_eq_zero (R := R) (C := C)
      (M := M) (N := N) h
  have ht' :
      t ∈ LinearMap.range (LinearMap.rTensor C (LinearMap.ker g).subtype) := by
    simpa [Function.Exact.linearMap_ker_eq (rTensor_exact C hexact hg)] using ht
  rw [← hker]
  simpa [LinearMap.rTensor] using ht'

omit [Coalgebra R C] [Comodule R C M] [Comodule R C N] [Module.Flat R C] in
private theorem rTensor_mkQ_map_subtype (B : Submodule R N) (t : B ⊗[R] C) :
    LinearMap.rTensor C B.mkQ
        (TensorProduct.map B.subtype (LinearMap.id : C →ₗ[R] C) t) = 0 := by
  induction t with
  | zero => simp
  | tmul b c =>
      have hb : B.mkQ (b : N) = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero B).2 b.property
      simp [LinearMap.rTensor, hb]
  | add x y hx hy =>
      simp [hx, hy]

private theorem comap_coact_mem (f : Comodule.Hom R C M N) (B : Subcomodule R C N)
    {m : M} (hm : m ∈ B.toSubmodule.comap f.toLinearMap) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range
        (TensorProduct.map (B.toSubmodule.comap f.toLinearMap).subtype
          (LinearMap.id : C →ₗ[R] C)) := by
  refine tensor_mem_range_comap (R := R) (C := C) (M := M) (N := N)
    B.toSubmodule f.toLinearMap ?_
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp]
  change LinearMap.rTensor C B.toSubmodule.mkQ
      (TensorProduct.map f.toLinearMap (LinearMap.id : C →ₗ[R] C)
        (Comodule.coact (R := R) (C := C) (M := M) m)) = 0
  rw [Comodule.Hom.map_coact_apply f m]
  rcases B.coact_mem hm with ⟨t, ht⟩
  change LinearMap.rTensor C B.toSubmodule.mkQ
      (Comodule.coact (R := R) (C := C) (M := N) (f.toLinearMap m)) = 0
  rw [← ht]
  exact rTensor_mkQ_map_subtype (R := R) (C := C) (N := N) B.toSubmodule t

/-- The inverse image of a subcomodule under a comodule morphism. -/
def comap (B : Subcomodule R C N) (f : Comodule.Hom R C M N) : Subcomodule R C M where
  carrier := B.toSubmodule.comap f.toLinearMap
  coact_mem' := by
    intro m hm
    exact comap_coact_mem f B hm

/-- The underlying submodule of an inverse-image subcomodule is the inverse image of the
underlying submodule. -/
@[simp]
theorem comap_toSubmodule (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    (B.comap f).toSubmodule = B.toSubmodule.comap f.toLinearMap :=
  rfl

/-- Membership in an inverse-image subcomodule. -/
@[simp]
theorem mem_comap {B : Subcomodule R C N} {f : Comodule.Hom R C M N} {m : M} :
    m ∈ B.comap f ↔ f m ∈ B :=
  Iff.rfl

/-- The inverse-image construction is monotone in the target subcomodule. -/
theorem comap_mono (f : Comodule.Hom R C M N) {B D : Subcomodule R C N} (hBD : B ≤ D) :
    B.comap f ≤ D.comap f := by
  intro m hm
  exact hBD hm

/-- The inverse image of the top subcomodule is top. -/
@[simp]
theorem comap_top (f : Comodule.Hom R C M N) : (⊤ : Subcomodule R C N).comap f = ⊤ := by
  ext m
  simp

/-- Images are left adjoint to inverse images for subcomodules. -/
theorem map_le_iff_le_comap {A : Subcomodule R C M} {B : Subcomodule R C N}
    {f : Comodule.Hom R C M N} :
    A.map f ≤ B ↔ A ≤ B.comap f := by
  rw [map_le_iff]
  rfl

/-- A subcomodule is contained in the inverse image of the image of a larger subcomodule. -/
theorem le_comap_map {A D : Subcomodule R C M} (hAD : A ≤ D) (f : Comodule.Hom R C M N) :
    A ≤ (D.map f).comap f := by
  rw [← map_le_iff_le_comap]
  exact map_mono f hAD

/-- The image of the inverse image of a subcomodule is contained in the subcomodule. -/
theorem map_comap_le (B : Subcomodule R C N) (f : Comodule.Hom R C M N) :
    (B.comap f).map f ≤ B := by
  rw [map_le_iff_le_comap]

/-- Inverse images compose contravariantly with comodule morphisms. -/
@[simp]
theorem comap_comap {P : Type y} [AddCommGroup P] [Module R P] [Comodule R C P]
    (B : Subcomodule R C P) (f : Comodule.Hom R C M N) (g : Comodule.Hom R C N P) :
    (B.comap g).comap f = B.comap (g.comp f) := by
  ext m
  rfl

/-- The inverse image along the identity comodule morphism is the original subcomodule. -/
@[simp]
theorem comap_id (B : Subcomodule R C M) :
    B.comap (Comodule.Hom.id R C M) = B := by
  ext m
  rfl

end Subcomodule

end TauCeti
