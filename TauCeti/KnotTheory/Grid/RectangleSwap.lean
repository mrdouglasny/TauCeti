/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Rectangle

/-!
# A grid rectangle move is a column transposition

An oriented rectangle `R : GridRectangleBetween x y` records the two side columns at which the
target state `y` differs from the source state `x`: at the initial side column `y` reads the
row `x` uses at the terminal side, and vice versa, while the two states agree away from the two
side columns. That is exactly the effect of swapping the two side columns of `x`, so the target
state is the column transposition `x.swapColumns R.left R.right`.

This file makes that identification precise and draws the point-set consequences: the two
states share all but two of their occupied squares, and each occupied square they do not share
is one of the four corners of the rectangle. The shared squares are exactly the intersection of
the two point sets, which has `n - 2` elements. These are the bookkeeping facts a Maslov or
Alexander grading-change computation across a rectangle rests on, and they let later
`∂² = 0`-style arguments reason about `x` and `y` through a single transposition.

## Main results

* `TauCeti.GridRectangleBetween.target_eq_swapColumns`: the target state of a rectangle is the
  source state with the two side columns swapped.
* `TauCeti.GridRectangleBetween.source_eq_swapColumns`: the symmetric statement recovering the
  source from the target.
* `TauCeti.GridRectangleBetween.mem_inter_pointSet_iff`: a square is shared by both states
  exactly when it belongs to the source and avoids the two side columns.
* `TauCeti.GridRectangleBetween.source_pointSet_eq`,
  `TauCeti.GridRectangleBetween.target_pointSet_eq`: each state's point set is the shared part
  together with its own two corners.
* `TauCeti.GridRectangleBetween.card_inter_pointSet`: the two states share exactly `n - 2`
  squares.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.2, "grading-change formulas across a rectangle", and Lane G.3, "The complexes and
`∂² = 0`". The column-transposition picture of a rectangle move follows Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 4.
-/

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- Pointwise form of the column-transposition identity: at each column the target state reads
the row the source state reads at the swapped column. -/
theorem target_apply (c : Fin n) : y c = x (Equiv.swap R.left R.right c) := by
  rcases eq_or_ne c R.left with h | hl
  · subst h
    rw [Equiv.swap_apply_left]
    exact R.map_left
  · rcases eq_or_ne c R.right with h | hr
    · subst h
      rw [Equiv.swap_apply_right]
      exact R.map_right
    · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
      exact R.map_of_ne c hl hr

/-- The target state of an oriented rectangle is the source state with its two side columns
swapped. The rectangle's defining equations -- the two side columns exchange their rows and the
other columns are unchanged -- are precisely the action of the column transposition. -/
theorem target_eq_swapColumns : y = x.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  exact target_apply R c

/-- The source state of an oriented rectangle is the target state with its two side columns
swapped: swapping the same pair of columns twice is the identity. -/
theorem source_eq_swapColumns : x = y.swapColumns R.left R.right := by
  refine GridState.ext fun c => ?_
  rw [GridState.swapColumns_apply]
  have h := target_apply R (Equiv.swap R.left R.right c)
  rw [Equiv.swap_apply_self] at h
  exact h.symm

/-- The underlying permutation of the target state is the source permutation precomposed with
the transposition of the two side columns. -/
theorem target_toPerm_eq :
    y.toPerm = (Equiv.swap R.left R.right).trans x.toPerm := by
  refine Equiv.ext fun c => ?_
  rw [Equiv.trans_apply]
  exact target_apply R c

/-- A square lies in the target state exactly when its column-transposed square lies in the
source state. -/
theorem mem_target_pointSet_iff (p : Fin n × Fin n) :
    p ∈ y.pointSet ↔ (Equiv.swap R.left R.right p.1, p.2) ∈ x.pointSet := by
  rw [GridState.mem_pointSet, GridState.mk_mem_pointSet, target_apply R p.1]

/-- The two side columns carry the four corners of a rectangle, so a square that the two states
share must avoid both side columns. Conversely, away from the side columns the two states agree,
so every source square off the side columns is shared. -/
theorem mem_inter_pointSet_iff (p : Fin n × Fin n) :
    p ∈ x.pointSet ∩ y.pointSet ↔
      p ∈ x.pointSet ∧ p.1 ≠ R.left ∧ p.1 ≠ R.right := by
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_, ?_⟩
    · rintro hleft
      have hb : p.2 = R.bottom := by
        simpa [hleft, bottom] using ((GridState.mem_pointSet x p).mp hx).symm
      have ht : p.2 = R.top := by
        simpa [hleft, top, R.map_left] using ((GridState.mem_pointSet y p).mp hy).symm
      exact R.bottom_ne_top (hb.symm.trans ht)
    · rintro hright
      have ht : p.2 = R.top := by
        simpa [hright, top] using ((GridState.mem_pointSet x p).mp hx).symm
      have hb : p.2 = R.bottom := by
        simpa [hright, bottom, R.map_right] using ((GridState.mem_pointSet y p).mp hy).symm
      exact R.bottom_ne_top (hb.symm.trans ht)
  · rintro ⟨hx, hleft, hright⟩
    refine ⟨hx, ?_⟩
    rw [GridState.mem_pointSet] at hx ⊢
    rw [R.map_of_ne p.1 hleft hright]
    exact hx

/-- The lower-left corner is not shared with the target state: it sits on a side column. -/
theorem left_bottom_notMem_inter :
    (R.left, R.bottom) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_inter_pointSet_iff R]
  rintro ⟨_, hleft, _⟩
  exact hleft rfl

/-- The upper-right corner is not shared with the target state: it sits on a side column. -/
theorem right_top_notMem_inter :
    (R.right, R.top) ∉ x.pointSet ∩ y.pointSet := by
  rw [mem_inter_pointSet_iff R]
  rintro ⟨_, _, hright⟩
  exact hright rfl

/-- The two corners of the source state are distinct. -/
theorem left_bottom_ne_right_top :
    ((R.left, R.bottom) : Fin n × Fin n) ≠ (R.right, R.top) := by
  rw [Ne, Prod.mk.injEq, not_and]
  intro h
  exact absurd h R.left_ne_right

/-- The source state's point set is its two shared columns' worth of squares -- the intersection
with the target -- together with its two own corners. -/
theorem source_pointSet_eq :
    x.pointSet =
      insert (R.left, R.bottom) (insert (R.right, R.top) (x.pointSet ∩ y.pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hx
    rcases eq_or_ne p.1 R.left with hleft | hleft
    · refine Or.inl ?_
      have : p.2 = R.bottom := by
        simpa [hleft, bottom] using ((GridState.mem_pointSet x p).mp hx).symm
      exact Prod.ext hleft this
    · rcases eq_or_ne p.1 R.right with hright | hright
      · refine Or.inr (Or.inl ?_)
        have : p.2 = R.top := by
          simpa [hright, top] using ((GridState.mem_pointSet x p).mp hx).symm
        exact Prod.ext hright this
      · exact Or.inr (Or.inr ((mem_inter_pointSet_iff R p).mpr ⟨hx, hleft, hright⟩))
  · rintro (rfl | rfl | hp)
    · exact R.left_bottom_mem_source
    · exact R.right_top_mem_source
    · exact Finset.mem_of_mem_inter_left hp

/-- The target state's point set is the shared part together with its own two corners. -/
theorem target_pointSet_eq :
    y.pointSet =
      insert (R.left, R.top) (insert (R.right, R.bottom) (x.pointSet ∩ y.pointSet)) := by
  ext p
  simp only [Finset.mem_insert]
  constructor
  · intro hy
    rcases eq_or_ne p.1 R.left with hleft | hleft
    · refine Or.inl ?_
      have : p.2 = R.top := by
        simpa [hleft, top, R.map_left] using ((GridState.mem_pointSet y p).mp hy).symm
      exact Prod.ext hleft this
    · rcases eq_or_ne p.1 R.right with hright | hright
      · refine Or.inr (Or.inl ?_)
        have : p.2 = R.bottom := by
          simpa [hright, bottom, R.map_right] using ((GridState.mem_pointSet y p).mp hy).symm
        exact Prod.ext hright this
      · refine Or.inr (Or.inr ?_)
        have hx : p ∈ x.pointSet := by
          rw [GridState.mem_pointSet] at hy ⊢
          rw [← R.map_of_ne p.1 hleft hright]
          exact hy
        exact (mem_inter_pointSet_iff R p).mpr ⟨hx, hleft, hright⟩
  · rintro (rfl | rfl | hp)
    · exact R.left_top_mem_target
    · exact R.right_bottom_mem_target
    · exact Finset.mem_of_mem_inter_right hp

include R in
/-- The source and target states share exactly `n - 2` squares: all of the source's `n` squares
except its two corners. -/
theorem card_inter_pointSet : (x.pointSet ∩ y.pointSet).card = n - 2 := by
  have hne : (R.right, R.top) ∉ x.pointSet ∩ y.pointSet := right_top_notMem_inter R
  have hne' :
      (R.left, R.bottom) ∉ insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact R.left_bottom_ne_right_top h
    · exact left_bottom_notMem_inter R h
  have hcard := congrArg Finset.card (source_pointSet_eq R)
  rw [GridState.card_pointSet, Finset.card_insert_of_notMem hne',
    Finset.card_insert_of_notMem hne] at hcard
  omega

end GridRectangleBetween

end TauCeti
