/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Pi

/-!
# Multiindices for Sobolev spaces

This file packages finitely supported functions `ι →₀ ℕ` as multiindices and records the
small amount of order bookkeeping needed to define weak derivatives of bounded total order.
For the PDE roadmap Lane A, the Sobolev norm on a finite-dimensional domain is indexed by
all multiindices of order at most `k`; the main structural fact here is that this indexing
type is finite when `ι` is finite.
-/

namespace TauCeti

/-- A multiindex on `ι`, represented as a finitely supported function `ι →₀ ℕ`. -/
abbrev MultiIndex (ι : Type*) : Type _ :=
  ι →₀ ℕ

namespace MultiIndex

variable {ι : Type*}

/-- The total order, or degree, of a multiindex. -/
def order (α : MultiIndex ι) : ℕ :=
  α.sum fun _ n => n

/-- The multiindex with one derivative in coordinate `i` and none elsewhere. -/
noncomputable def unit (i : ι) : MultiIndex ι :=
  Finsupp.single i 1

@[simp]
lemma order_zero : order (0 : MultiIndex ι) = 0 := by
  simp [order]

@[simp]
lemma order_single (i : ι) (n : ℕ) : order (Finsupp.single i n : MultiIndex ι) = n := by
  simp [order]

@[simp]
lemma order_unit (i : ι) : order (unit i : MultiIndex ι) = 1 := by
  simp [unit]

lemma order_add (α β : MultiIndex ι) :
    order (α + β) = order α + order β := by
  classical
  simp [order, Finsupp.sum_add_index']

lemma order_le_order_add_left (α β : MultiIndex ι) : order α ≤ order (α + β) := by
  rw [order_add]
  exact Nat.le_add_right _ _

lemma order_le_order_add_right (α β : MultiIndex ι) : order β ≤ order (α + β) := by
  rw [order_add]
  exact Nat.le_add_left _ _

lemma order_mono {α β : MultiIndex ι} (h : α ≤ β) :
    order α ≤ order β := by
  classical
  exact Finsupp.sum_le_sum_index h (fun _ _ => monotone_id) (fun _ _ => rfl)

lemma order_eq_sum [Fintype ι] (α : MultiIndex ι) : order α = ∑ i, α i := by
  simp [order, Finsupp.sum_fintype]

lemma apply_le_order (α : MultiIndex ι) (i : ι) : α i ≤ order α := by
  exact Finsupp.single_eval_le_sum (f := α) (g := fun n => n) rfl (fun n => Nat.zero_le n) i

lemma eq_zero_of_order_eq_zero {α : MultiIndex ι} (h : order α = 0) : α = 0 := by
  ext i
  have hle : α i ≤ 0 := by
    simpa [h] using apply_le_order α i
  exact Nat.eq_zero_of_le_zero hle

@[simp]
lemma order_eq_zero_iff {α : MultiIndex ι} : order α = 0 ↔ α = 0 :=
  ⟨eq_zero_of_order_eq_zero, fun h => by simp [h]⟩

@[simp]
lemma zero_lt_order_iff {α : MultiIndex ι} : 0 < order α ↔ α ≠ 0 := by
  constructor
  · intro h hα
    simp [hα] at h
  · intro h
    exact Nat.pos_of_ne_zero fun horder => h (order_eq_zero_iff.mp horder)

lemma order_pos_of_ne_zero {α : MultiIndex ι} (hα : α ≠ 0) : 0 < order α :=
  zero_lt_order_iff.mpr hα

lemma order_eq_one_iff {α : MultiIndex ι} : order α = 1 ↔ ∃ i, α = unit i := by
  rw [order, Finsupp.sum_eq_one_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa [unit] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa [unit] using hi⟩

@[simp]
lemma unit_apply_self (i : ι) : unit i i = 1 := by
  classical
  simp [unit]

lemma unit_apply_ne {i j : ι} (hij : j ≠ i) : unit i j = 0 := by
  classical
  simp [unit, hij]

lemma unit_le_iff (i : ι) (α : MultiIndex ι) : unit i ≤ α ↔ 1 ≤ α i := by
  classical
  constructor
  · intro h
    simpa [unit] using h i
  · intro hi j
    by_cases hji : j = i
    · subst j
      simpa [unit] using hi
    · simp [unit, hji]

/-- Multiindices whose total order is at most `k`, as a subtype. -/
abbrev DegreeLE (ι : Type*) (k : ℕ) : Type _ :=
  { α : MultiIndex ι // order α ≤ k }

section DegreeLE

variable {k : ℕ}

/-- A bounded-order multiindex as a function into `Fin (k + 1)`.

The coordinate bound is the direct reason why bounded-order multiindices form a finite type. -/
def toBoundedFun (α : DegreeLE ι k) : ι → Fin (k + 1) :=
  fun i => ⟨α.1 i, Nat.lt_succ_of_le ((apply_le_order α.1 i).trans α.2)⟩

lemma toBoundedFun_injective : Function.Injective (toBoundedFun (ι := ι) (k := k)) := by
  intro α β h
  ext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance degreeLEFintype [Fintype ι] : Fintype (DegreeLE ι k) := by
  classical
  exact Fintype.ofInjective (toBoundedFun (ι := ι) (k := k)) toBoundedFun_injective

/-- There are only finitely many multiindices of order at most `k` on a finite index type. -/
lemma finite_setOf_order_le [Finite ι] (k : ℕ) : {α : MultiIndex ι | order α ≤ k}.Finite := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype (DegreeLE ι k) := degreeLEFintype (ι := ι) (k := k)
  exact @Set.toFinite (MultiIndex ι) {α | order α ≤ k} (by
    change Finite (DegreeLE ι k)
    exact Finite.of_fintype _)

@[simp]
lemma mem_degreeLE_iff (α : MultiIndex ι) : α ∈ {α : MultiIndex ι | order α ≤ k} ↔
    order α ≤ k :=
  Iff.rfl

end DegreeLE

end MultiIndex

end TauCeti
