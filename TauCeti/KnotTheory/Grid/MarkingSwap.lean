/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import TauCeti.KnotTheory.Grid.GradingInteger

/-!
# The marking-swap symmetry of a grid diagram

A grid diagram carries two marking states, the `O`-markings and the `X`-markings, on equal
footing: the only condition relating them is that no square carries both. Exchanging the two
marking states is therefore again a grid diagram, the *marking swap* `G.swapMarkings`. This file
records that operation and its effect on the Maslov and Alexander gradings.

Because the two Maslov gradings `M_O` and `M_X` are built from the `O`- and `X`-markings by the
*same* formula, the marking swap simply exchanges them. The Alexander grading
`A = (M_O − M_X) / 2 − (n − 1) / 2` is antisymmetric in that exchange, so the swap negates it up
to the constant normalization shift: `A_swap(x) = −A(x) − (n − 1)`. The integer-valued gradings
transform the same way.

The marking swap is the diagram-level operation behind the conjugation symmetry of grid
homology, the symmetry that ultimately pairs the generator in bigrading `(M, A)` with one in
bigrading `(M − 2A, −A)`. Here we stay purely at the combinatorial grading level, which is all
that the existing grading API supports.

## Main definitions

* `TauCeti.GridDiagram.swapMarkings`: the grid diagram obtained by exchanging the `O`- and
  `X`-marking states.

## Main results

* `TauCeti.GridDiagram.swapMarkings_swapMarkings`: the marking swap is an involution.
* `TauCeti.GridDiagram.transpose_swapMarkings`: the marking swap commutes with the diagonal
  reflection.
* `TauCeti.GridDiagram.maslovO_swapMarkings`, `TauCeti.GridDiagram.maslovX_swapMarkings`: the two
  Maslov gradings are exchanged by the marking swap.
* `TauCeti.GridDiagram.alexander_swapMarkings`: the Alexander grading is negated up to the
  normalization shift.
* `TauCeti.GridDiagram.maslovOℤ_swapMarkings`, `TauCeti.GridDiagram.maslovXℤ_swapMarkings`,
  `TauCeti.GridDiagram.alexanderTwoℤ_swapMarkings`: the integer-valued gradings transform the
  same way.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 8, "Symmetries
and the genus bound", supplying the marking-exchange symmetry of the gradings. The conjugation
symmetry it underlies is treated in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 5.3.
-/

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The marking swap of a grid diagram, obtained by exchanging the `O`- and `X`-marking states.

The defining no-double-marking condition is symmetric in the two marking states, so the swap is
again a grid diagram. -/
def swapMarkings (G : GridDiagram n) : GridDiagram n where
  O := G.X
  X := G.O
  disjoint c := (G.disjoint c).symm

/-- The `O`-marking state of the marking swap is the original `X`-marking state. -/
@[simp]
theorem swapMarkings_O : G.swapMarkings.O = G.X :=
  rfl

/-- The `X`-marking state of the marking swap is the original `O`-marking state. -/
@[simp]
theorem swapMarkings_X : G.swapMarkings.X = G.O :=
  rfl

/-- The `O`-marking set of the marking swap is the original `X`-marking set. -/
@[simp]
theorem swapMarkings_OSet : G.swapMarkings.OSet = G.XSet :=
  rfl

/-- The `X`-marking set of the marking swap is the original `O`-marking set. -/
@[simp]
theorem swapMarkings_XSet : G.swapMarkings.XSet = G.OSet :=
  rfl

/-- Membership in the marking swap's `O`-marking set is membership in the original
`X`-marking set. -/
@[simp]
theorem mem_OSet_swapMarkings (p : Fin n × Fin n) :
    p ∈ G.swapMarkings.OSet ↔ p ∈ G.XSet :=
  Iff.rfl

/-- Membership in the marking swap's `X`-marking set is membership in the original
`O`-marking set. -/
@[simp]
theorem mem_XSet_swapMarkings (p : Fin n × Fin n) :
    p ∈ G.swapMarkings.XSet ↔ p ∈ G.OSet :=
  Iff.rfl

/-- The marking swap is an involution: exchanging the two marking states twice restores the
grid diagram. -/
@[simp]
theorem swapMarkings_swapMarkings : G.swapMarkings.swapMarkings = G :=
  rfl

/-- The marking swap commutes with the diagonal reflection of a grid diagram. -/
@[simp]
theorem transpose_swapMarkings : G.swapMarkings.transpose = G.transpose.swapMarkings :=
  rfl

/-- The marking swap exchanges the `O`-marking `J`-pairing with the `X`-marking `J`-pairing. -/
@[simp]
theorem JO_swapMarkings (x : GridState n) : G.swapMarkings.JO x = G.JX x :=
  rfl

/-- The marking swap exchanges the `X`-marking `J`-pairing with the `O`-marking `J`-pairing. -/
@[simp]
theorem JX_swapMarkings (x : GridState n) : G.swapMarkings.JX x = G.JO x :=
  rfl

/-- The marking swap exchanges the two Maslov gradings: `M_O` of the swap is `M_X`. -/
theorem maslovO_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovO x = G.maslovX x := by
  rw [maslovO_def, maslovX_def, swapMarkings_OSet]

/-- The marking swap exchanges the two Maslov gradings: `M_X` of the swap is `M_O`. -/
theorem maslovX_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovX x = G.maslovO x := by
  rw [maslovX_def, maslovO_def, swapMarkings_XSet]

/-- The marking swap negates the Alexander grading, up to the constant normalization shift:
`A_swap(x) = −A(x) − (n − 1)`. The grading is built antisymmetrically from the two Maslov
gradings, which the swap exchanges, while the shift depends only on the grid size. -/
theorem alexander_swapMarkings (x : GridState n) :
    G.swapMarkings.alexander x = -G.alexander x - (((n : ℤ) - 1 : ℤ) : ℚ) := by
  rw [alexander_def, alexander_def, maslovO_swapMarkings, maslovX_swapMarkings]
  ring

/-- The marking swap exchanges the integer-valued Maslov gradings. -/
theorem maslovOℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovOℤ x = G.maslovXℤ x := by
  rw [maslovOℤ_def, maslovXℤ_def, swapMarkings_OSet]

/-- The marking swap exchanges the integer-valued Maslov gradings. -/
theorem maslovXℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.maslovXℤ x = G.maslovOℤ x := by
  rw [maslovXℤ_def, maslovOℤ_def, swapMarkings_XSet]

/-- The marking swap negates the integer numerator of twice the Alexander grading, up to twice
the normalization shift: `2·A_swap(x) = −2·A(x) − 2(n − 1)`. -/
theorem alexanderTwoℤ_swapMarkings (x : GridState n) :
    G.swapMarkings.alexanderTwoℤ x = -G.alexanderTwoℤ x - 2 * ((n : ℤ) - 1) := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_swapMarkings, maslovXℤ_swapMarkings]
  ring

end GridDiagram

end TauCeti
