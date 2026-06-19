/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# Almost complex structures as complex module structures

A pointwise almost complex structure `J` on a real module `V` (a real-linear endomorphism with
`J ∘ J = -1`, from `TauCeti.AlmostComplexStructure`) is the same data as a complex vector space
structure on `V` extending the real one: scalar multiplication by `a + b·i` is `a • v + b • J v`,
and conversely multiplication by `i` recovers `J`. This file makes that classical correspondence
(McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Section 2.1) precise.

The forward direction `AlmostComplexStructure.complexModule` turns `J` into a `Module ℂ V`; it is
deliberately a `def`, not an instance, because the complex structure depends on the chosen `J` and
is not canonical. The backward direction `AlmostComplexStructure.ofComplexModule` reads an almost
complex structure off any complex module structure compatible with the real scalars. The two are
mutually inverse: `ofComplexModule` applied to `complexModule J` returns `J`.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexModule`: the `Module ℂ V` with
  `(a + b·i) • v = a • v + b • J v`.
* `TauCeti.AlmostComplexStructure.complexModule_smul_def`: the defining scalar action.
* `TauCeti.AlmostComplexStructure.complexModule_I_smul`: `i • v = J v` in the induced module.
* `TauCeti.AlmostComplexStructure.complexModule_ofReal_smul`: the induced action restricts to the
  original real action.
* `TauCeti.AlmostComplexStructure.complexModule_isScalarTower`: `ℝ`, `ℂ`, `V` form a scalar tower.
* `TauCeti.AlmostComplexStructure.ofComplexModule`: the almost complex structure `v ↦ i • v` on a
  complex module.
* `TauCeti.AlmostComplexStructure.ofComplexModule_complexModule`: the round trip recovers `J`.
-/

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*}

section ToComplex

variable [AddCommGroup V] [Module ℝ V]

/-- The complex vector space structure on a real module `V` induced by an almost complex
structure `J`: the scalar `a + b·i` acts as `a • v + b • J v`.

This is a `def` rather than an instance because the complex structure is not canonical: it depends
on the chosen `J`. Restricted to the real scalars it is the original `Module ℝ V`
(`complexModule_isScalarTower`, `complexModule_ofReal_smul`). -/
@[reducible]
def complexModule (J : AlmostComplexStructure V) : Module ℂ V where
  smul z v := z.re • v + z.im • J v
  one_smul v := by
    change (1 : ℂ).re • v + (1 : ℂ).im • J v = v
    rw [Complex.one_re, Complex.one_im, one_smul, zero_smul, add_zero]
  mul_smul a b v := by
    change (a * b).re • v + (a * b).im • J v =
      a.re • (b.re • v + b.im • J v) + a.im • J (b.re • v + b.im • J v)
    have hadd : ∀ x y : V, J (x + y) = J x + J y := fun x y => J.toLinearMap.map_add x y
    have hsmul : ∀ (c : ℝ) (x : V), J (c • x) = c • J x := fun c x => J.toLinearMap.map_smul c x
    have hJ : J (b.re • v + b.im • J v) = b.re • J v - b.im • v := by
      rw [hadd, hsmul, hsmul, J.apply_apply, smul_neg, sub_eq_add_neg]
    rw [hJ, Complex.mul_re, Complex.mul_im]
    module
  smul_zero a := by
    change a.re • (0 : V) + a.im • J 0 = 0
    rw [J.toLinearMap.map_zero, smul_zero, smul_zero, add_zero]
  smul_add a v w := by
    change a.re • (v + w) + a.im • J (v + w) = (a.re • v + a.im • J v) + (a.re • w + a.im • J w)
    rw [J.toLinearMap.map_add, smul_add, smul_add]
    abel
  add_smul a b v := by
    change (a + b).re • v + (a + b).im • J v = (a.re • v + a.im • J v) + (b.re • v + b.im • J v)
    rw [Complex.add_re, Complex.add_im, add_smul, add_smul]
    abel
  zero_smul v := by
    change (0 : ℂ).re • v + (0 : ℂ).im • J v = 0
    rw [Complex.zero_re, Complex.zero_im, zero_smul, zero_smul, add_zero]

/-- The defining formula for the complex action induced by an almost complex structure. -/
lemma complexModule_smul_def (J : AlmostComplexStructure V) (z : ℂ) (v : V) :
    letI := J.complexModule
    z • v = z.re • v + z.im • J v :=
  rfl

/-- In the induced complex structure, multiplication by `i` is `J`. -/
lemma complexModule_I_smul (J : AlmostComplexStructure V) (v : V) :
    letI := J.complexModule
    (Complex.I) • v = J v := by
  letI := J.complexModule
  rw [complexModule_smul_def, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_add]

/-- The induced complex action restricts along `ℝ → ℂ` to the original real action. -/
lemma complexModule_ofReal_smul (J : AlmostComplexStructure V) (r : ℝ) (v : V) :
    letI := J.complexModule
    (r : ℂ) • v = r • v := by
  letI := J.complexModule
  rw [complexModule_smul_def, Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-- `ℝ`, `ℂ`, and `V` form a scalar tower for the induced complex structure: the real scalars act
the same whether through `ℝ` or through `ℂ`. -/
lemma complexModule_isScalarTower (J : AlmostComplexStructure V) :
    letI := J.complexModule
    IsScalarTower ℝ ℂ V := by
  letI := J.complexModule
  refine ⟨fun a b v => ?_⟩
  rw [complexModule_smul_def, complexModule_smul_def, Complex.smul_re, Complex.smul_im]
  simp only [smul_eq_mul]
  module

end ToComplex

section OfComplex

variable [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]

/-- The almost complex structure `v ↦ i • v` on a complex module whose real scalars are compatible
with the ambient real structure. This is the inverse construction to `complexModule`. -/
def ofComplexModule (V : Type*) [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    AlmostComplexStructure V where
  toLinearMap := (LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ
  square_neg := by
    ext v
    simp [smul_smul, Complex.I_mul_I]

@[simp]
lemma ofComplexModule_apply (v : V) : ofComplexModule V v = Complex.I • v :=
  rfl

end OfComplex

/-- Two almost complex structures agreeing pointwise are equal. -/
lemma ext {V : Type*} [AddCommGroup V] [Module ℝ V] {J K : AlmostComplexStructure V}
    (h : ∀ v, J v = K v) : J = K := by
  cases J
  cases K
  congr 1
  exact LinearMap.ext h

/-- Reading the almost complex structure back off the induced complex module recovers `J`: the two
constructions are mutually inverse. -/
lemma ofComplexModule_complexModule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : AlmostComplexStructure V) :
    letI := J.complexModule
    letI := J.complexModule_isScalarTower
    ofComplexModule V = J := by
  letI := J.complexModule
  letI := J.complexModule_isScalarTower
  refine ext fun v => ?_
  rw [ofComplexModule_apply, complexModule_I_smul]

end AlmostComplexStructure

end TauCeti
