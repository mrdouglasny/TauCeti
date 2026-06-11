/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Prod
import TauCeti.Algebra.Coalgebra.Comodule.Hom

/-!
# Products of comodules

For two right `C`-comodules `M` and `N` over an `R`-coalgebra `C`, this file equips the
product module `M × N` with the canonical right `C`-coaction
`(m, n) ↦ ι_M(ρ_M m) + ι_N(ρ_N n)`, where `ι_M`, `ι_N` are the inclusions into the first and
second summand. With this structure the projections `M × N → M`, `M × N → N` and the
inclusions `M → M × N`, `N → M × N` are comodule morphisms, and the universal properties of
the product and the coproduct hold, so `M × N` is simultaneously the product and the coproduct
of `M` and `N`: a direct sum of comodules.

Together with the zero object (`TauCeti.Algebra.Coalgebra.Comodule.Zero`) and the preadditive
structure (`TauCeti.Algebra.Coalgebra.Comodule.Preadditive`) this supplies the binary-biproduct
ingredient of the (finite-dimensional) comodule representation category called for in Layer 1
of the reductive-groups roadmap.

## Main definitions

* `TauCeti.Comodule.instProd`: the right `C`-comodule structure on `M × N`.
* `TauCeti.Comodule.Hom.fst`, `TauCeti.Comodule.Hom.snd`: the projection comodule morphisms.
* `TauCeti.Comodule.Hom.inl`, `TauCeti.Comodule.Hom.inr`: the inclusion comodule morphisms.
* `TauCeti.Comodule.Hom.prod`, `TauCeti.Comodule.Hom.coprod`: the morphisms induced by the
  universal properties of the product and the coproduct, characterized by
  `fst_comp_prod`/`snd_comp_prod` and `coprod_comp_inl`/`coprod_comp_inr`, with the
  biproduct relations `fst_comp_inl`, `snd_comp_inl`, `fst_comp_inr`, `snd_comp_inr`.

## References

This is the standard direct sum of comodules; see for example Sweedler, *Hopf Algebras*,
Chapter 2. It supplies a binary-biproduct prerequisite for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1, "Comodules over a coalgebra/Hopf
algebra". It reuses Mathlib's `TensorProduct.assoc` associativity coherence and the
`rTensor`/`lTensor` calculus from `Mathlib.LinearAlgebra.TensorProduct.Map`.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w x y

namespace Comodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x} {P : Type y}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]
variable [AddCommMonoid P] [Module R P] [Comodule R C P]

local notation "ρM" => coact (R := R) (C := C) (M := M)
local notation "ρN" => coact (R := R) (C := C) (M := N)

omit [Coalgebra R C] [Comodule R C M] in
/-- A naturality lemma for the tensor associator against `rTensor` in the first factor,
phrased so it can rewrite the comodule coassociativity calculation below. -/
theorem assoc_rTensor_rTensor_apply {Q : Type*} [AddCommMonoid Q] [Module R Q] (f : M →ₗ[R] Q)
    (x : (M ⊗[R] C) ⊗[R] C) :
    TensorProduct.assoc R Q C C ((f.rTensor C).rTensor C x)
      = f.rTensor (C ⊗[R] C) (TensorProduct.assoc R M C C x) := by
  induction x with
  | zero => simp
  | tmul a c =>
    induction a with
    | zero => simp
    | tmul m c' => simp
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The coaction of the product comodule `M × N`: coact on each factor, then include into the
corresponding summand. -/
noncomputable def prodCoact : (M × N) →ₗ[R] (M × N) ⊗[R] C :=
  (LinearMap.inl R M N).rTensor C ∘ₗ ρM ∘ₗ LinearMap.fst R M N
    + (LinearMap.inr R M N).rTensor C ∘ₗ ρN ∘ₗ LinearMap.snd R M N

@[simp]
theorem prodCoact_comp_inl :
    prodCoact ∘ₗ LinearMap.inl R M N = (LinearMap.inl R M N).rTensor C ∘ₗ ρM := by
  ext m; simp [prodCoact]

@[simp]
theorem prodCoact_comp_inr :
    prodCoact ∘ₗ LinearMap.inr R M N = (LinearMap.inr R M N).rTensor C ∘ₗ ρN := by
  ext n; simp [prodCoact]

theorem prodCoact_apply (m : M) (n : N) :
    prodCoact (m, n) = (LinearMap.inl R M N).rTensor C (ρM m)
      + (LinearMap.inr R M N).rTensor C (ρN n) := by
  simp [prodCoact]

private theorem prodCoassoc_inl (m : M) :
    TensorProduct.assoc R (M × N) C C (prodCoact.rTensor C (prodCoact (LinearMap.inl R M N m)))
      = Coalgebra.comul.lTensor (M × N) (prodCoact (LinearMap.inl R M N m)) := by
  rw [show prodCoact (LinearMap.inl R M N m) = (LinearMap.inl R M N).rTensor C (ρM m) from
      congr($prodCoact_comp_inl m)]
  rw [← LinearMap.comp_apply (prodCoact.rTensor C), ← LinearMap.rTensor_comp,
    prodCoact_comp_inl, LinearMap.rTensor_comp]
  simp only [LinearMap.comp_apply, assoc_rTensor_rTensor_apply, coassoc_apply]
  rw [← LinearMap.comp_apply (Coalgebra.comul.lTensor (M × N)),
    LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply (LinearMap.rTensor (C ⊗[R] C) _),
    LinearMap.rTensor_comp_lTensor]

private theorem prodCoassoc_inr (n : N) :
    TensorProduct.assoc R (M × N) C C (prodCoact.rTensor C (prodCoact (LinearMap.inr R M N n)))
      = Coalgebra.comul.lTensor (M × N) (prodCoact (LinearMap.inr R M N n)) := by
  rw [show prodCoact (LinearMap.inr R M N n) = (LinearMap.inr R M N).rTensor C (ρN n) from
      congr($prodCoact_comp_inr n)]
  rw [← LinearMap.comp_apply (prodCoact.rTensor C), ← LinearMap.rTensor_comp,
    prodCoact_comp_inr, LinearMap.rTensor_comp]
  simp only [LinearMap.comp_apply, assoc_rTensor_rTensor_apply, coassoc_apply]
  rw [← LinearMap.comp_apply (Coalgebra.comul.lTensor (M × N)),
    LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply (LinearMap.rTensor (C ⊗[R] C) _),
    LinearMap.rTensor_comp_lTensor]

private theorem prodCounit_inl (m : M) :
    (Coalgebra.counit : C →ₗ[R] R).lTensor (M × N) (prodCoact (LinearMap.inl R M N m))
      = (LinearMap.inl R M N m) ⊗ₜ[R] (1 : R) := by
  rw [show prodCoact (LinearMap.inl R M N m) = (LinearMap.inl R M N).rTensor C (ρM m) from
      congr($prodCoact_comp_inl m)]
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply, lTensor_counit_coact]
  simp

private theorem prodCounit_inr (n : N) :
    (Coalgebra.counit : C →ₗ[R] R).lTensor (M × N) (prodCoact (LinearMap.inr R M N n))
      = (LinearMap.inr R M N n) ⊗ₜ[R] (1 : R) := by
  rw [show prodCoact (LinearMap.inr R M N n) = (LinearMap.inr R M N).rTensor C (ρN n) from
      congr($prodCoact_comp_inr n)]
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply, lTensor_counit_coact]
  simp

/-- The product `M × N` of two right `C`-comodules, with the summandwise coaction. -/
noncomputable instance instProd : Comodule R C (M × N) where
  coact := prodCoact
  coassoc := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, n⟩ := x
    rw [show (m, n) = LinearMap.inl R M N m + LinearMap.inr R M N n by simp]
    simp only [map_add, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [prodCoassoc_inl, prodCoassoc_inr]
  lTensor_counit_comp_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp only [LinearMap.comp_apply]
      rw [prodCounit_inl]
      rfl
    · ext n
      simp only [LinearMap.comp_apply]
      rw [prodCounit_inr]
      rfl

@[simp]
theorem prod_coact_apply (m : M) (n : N) :
    coact (R := R) (C := C) (M := M × N) (m, n) = (LinearMap.inl R M N).rTensor C (ρM m)
      + (LinearMap.inr R M N).rTensor C (ρN n) :=
  prodCoact_apply m n

@[simp]
theorem prod_coact_inl (m : M) :
    coact (R := R) (C := C) (M := M × N) (LinearMap.inl R M N m)
      = (LinearMap.inl R M N).rTensor C (ρM m) :=
  congr($prodCoact_comp_inl m)

@[simp]
theorem prod_coact_inr (n : N) :
    coact (R := R) (C := C) (M := M × N) (LinearMap.inr R M N n)
      = (LinearMap.inr R M N).rTensor C (ρN n) :=
  congr($prodCoact_comp_inr n)

namespace Hom

@[simp] theorem apply_zero (f : Hom R C M N) : f (0 : M) = 0 :=
  map_zero f.toLinearMap

/-- The first projection `M × N → M` as a comodule morphism. -/
def fst : Hom R C (M × N) M where
  toLinearMap := LinearMap.fst R M N
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp
    · ext n
      simp

/-- The second projection `M × N → N` as a comodule morphism. -/
def snd : Hom R C (M × N) N where
  toLinearMap := LinearMap.snd R M N
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      simp
    · ext n
      simp

/-- The first inclusion `M → M × N` as a comodule morphism. -/
def inl : Hom R C M (M × N) where
  toLinearMap := LinearMap.inl R M N
  map_coact := (prodCoact_comp_inl).symm

/-- The second inclusion `N → M × N` as a comodule morphism. -/
def inr : Hom R C N (M × N) where
  toLinearMap := LinearMap.inr R M N
  map_coact := (prodCoact_comp_inr).symm

@[simp] theorem fst_apply (x : M × N) : (fst : Hom R C (M × N) M) x = x.1 := rfl
@[simp] theorem snd_apply (x : M × N) : (snd : Hom R C (M × N) N) x = x.2 := rfl
@[simp] theorem inl_apply (m : M) : (inl : Hom R C M (M × N)) m = (m, 0) := rfl
@[simp] theorem inr_apply (n : N) : (inr : Hom R C N (M × N)) n = (0, n) := rfl

/-- The morphism into a product induced by a pair of morphisms. -/
def prod (f : Hom R C P M) (g : Hom R C P N) : Hom R C P (M × N) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  map_coact := by
    have hdecomp : f.toLinearMap.prod g.toLinearMap
        = (LinearMap.inl R M N).comp f.toLinearMap
          + (LinearMap.inr R M N).comp g.toLinearMap := by ext q <;> simp
    refine LinearMap.ext fun p => ?_
    have hf := LinearMap.congr_fun f.map_coact p
    have hg := LinearMap.congr_fun g.map_coact p
    simp only [LinearMap.comp_apply] at hf hg
    change TensorProduct.map (f.toLinearMap.prod g.toLinearMap) LinearMap.id (coact p)
      = coact (R := R) (C := C) (M := M × N) ((f.toLinearMap.prod g.toLinearMap) p)
    rw [hdecomp, TensorProduct.map_add_left, LinearMap.add_apply,
      ← LinearMap.rTensor_map, ← LinearMap.rTensor_map, hf, hg]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_inl, LinearMap.coe_inr,
      Prod.mk_add_mk, add_zero, zero_add, prod_coact_apply]

/-- The morphism out of a coproduct induced by a pair of morphisms. -/
def coprod (f : Hom R C M P) (g : Hom R C N P) : Hom R C (M × N) P where
  toLinearMap := f.toLinearMap.coprod g.toLinearMap
  map_coact := by
    apply LinearMap.prod_ext
    · ext m
      have hf := LinearMap.congr_fun f.map_coact m
      simp only [LinearMap.comp_apply] at hf ⊢
      rw [prod_coact_inl, LinearMap.map_rTensor, LinearMap.coprod_inl, hf]
      congr 1
      simp only [LinearMap.coprod_apply, LinearMap.inl_apply, map_zero, add_zero]
    · ext n
      have hg := LinearMap.congr_fun g.map_coact n
      simp only [LinearMap.comp_apply] at hg ⊢
      rw [prod_coact_inr, LinearMap.map_rTensor, LinearMap.coprod_inr, hg]
      congr 1
      simp only [LinearMap.coprod_apply, LinearMap.inr_apply, map_zero, zero_add]

@[simp] theorem prod_apply (f : Hom R C P M) (g : Hom R C P N) (p : P) :
    (prod f g) p = (f p, g p) := rfl

@[simp] theorem coprod_apply (f : Hom R C M P) (g : Hom R C N P) (x : M × N) :
    (coprod f g) x = f x.1 + g x.2 := rfl

@[simp] theorem fst_comp_prod (f : Hom R C P M) (g : Hom R C P N) :
    comp fst (prod f g) = f := by ext p; simp

@[simp] theorem snd_comp_prod (f : Hom R C P M) (g : Hom R C P N) :
    comp snd (prod f g) = g := by ext p; simp

@[simp] theorem coprod_comp_inl (f : Hom R C M P) (g : Hom R C N P) :
    comp (coprod f g) inl = f := by ext m; simp

@[simp] theorem coprod_comp_inr (f : Hom R C M P) (g : Hom R C N P) :
    comp (coprod f g) inr = g := by ext n; simp

@[simp] theorem fst_comp_inl : comp (fst : Hom R C (M × N) M) inl = id R C M := by
  ext m; simp

@[simp] theorem snd_comp_inl : comp (snd : Hom R C (M × N) N) inl = 0 := by
  ext m; simp

@[simp] theorem fst_comp_inr : comp (fst : Hom R C (M × N) M) inr = 0 := by
  ext n; simp

@[simp] theorem snd_comp_inr : comp (snd : Hom R C (M × N) N) inr = id R C N := by
  ext n; simp

end Hom

end Comodule


end TauCeti
