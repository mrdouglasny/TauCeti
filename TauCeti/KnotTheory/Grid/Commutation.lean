/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Diagram

/-!
# Row and column relabeling for grid diagrams

This file records the elementary row and column relabeling operations on grid states and
grid diagrams. The adjacent-row and adjacent-column swaps are the diagram-level operations
underlying commutation moves; the later commutation maps and invariance proofs can add the
non-interleaving hypotheses and rectangle-counting constructions on top of these total
operations.

## Main definitions

* `TauCeti.GridState.relabelRows`: postcompose a grid state with a row permutation.
* `TauCeti.GridState.relabelColumns`: precompose a grid state with the inverse of a column
  permutation.
* `TauCeti.GridDiagram.relabelRows`, `TauCeti.GridDiagram.relabelColumns`: the corresponding
  relabelings of the `O` and `X` markings of a grid diagram.
* `TauCeti.GridDiagram.swapRows`, `TauCeti.GridDiagram.swapColumns`: row and column swaps.

## References

This supplies a prerequisite for `TauCetiRoadmap/HeegaardFloer/README.md`, Lane G.5,
"Invariance over `𝔽₂`. Grid moves = commutation + (de)stabilization." It isolates the
underlying grid-diagram relabeling used by row and column commutations in the grid homology
construction of Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Relabel the rows of a grid state by a permutation of `Fin n`.

If `ρ` is the row permutation, the point in column `c` moves from row `x c` to row
`ρ (x c)`. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => ρ (x c)
      invFun := fun r => x.toPerm.symm (ρ.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

/-- Relabel the columns of a grid state by a permutation of `Fin n`.

The point in the old column `c` appears in the new column `κ c`, so the row in a new column
`c` is read from the old column `κ.symm c`. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n) : GridState n where
  toPerm :=
    { toFun := fun c => x (κ.symm c)
      invFun := fun r => κ (x.toPerm.symm r)
      left_inv := by
        intro c
        simp
      right_inv := by
        intro r
        simp }

/-- Row relabeling evaluates by applying the row permutation to the old row. -/
@[simp]
theorem relabelRows_apply (ρ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelRows ρ c = ρ (x c) :=
  rfl

/-- Column relabeling evaluates by reading the old state at the inverse column. -/
@[simp]
theorem relabelColumns_apply (κ : Equiv.Perm (Fin n)) (x : GridState n) (c : Fin n) :
    x.relabelColumns κ c = x (κ.symm c) :=
  rfl

/-- Relabeling rows by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelRows_refl (x : GridState n) : x.relabelRows (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Relabeling columns by the identity permutation does not change a grid state. -/
@[simp]
theorem relabelColumns_refl (x : GridState n) :
    x.relabelColumns (Equiv.refl (Fin n)) = x := by
  ext c
  simp

/-- Successive row relabelings compose. -/
@[simp]
theorem relabelRows_relabelRows (ρ σ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelRows σ = x.relabelRows (ρ.trans σ) := by
  ext c
  simp

/-- Successive column relabelings compose. -/
@[simp]
theorem relabelColumns_relabelColumns (κ τ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelColumns κ).relabelColumns τ = x.relabelColumns (κ.trans τ) := by
  ext c
  simp

/-- Row and column relabeling commute on grid states. -/
theorem relabelRows_relabelColumns (ρ κ : Equiv.Perm (Fin n)) (x : GridState n) :
    (x.relabelRows ρ).relabelColumns κ = (x.relabelColumns κ).relabelRows ρ := by
  ext c
  simp

/-- Membership in the point set after a row relabeling. -/
@[simp]
theorem mem_pointSet_relabelRows (ρ : Equiv.Perm (Fin n)) (x : GridState n)
    (p : Fin n × Fin n) :
    p ∈ (x.relabelRows ρ).pointSet ↔ (p.1, ρ.symm p.2) ∈ x.pointSet := by
  simp only [mem_pointSet, relabelRows_apply]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

/-- Membership in the point set after a column relabeling. -/
@[simp]
theorem mem_pointSet_relabelColumns (κ : Equiv.Perm (Fin n)) (x : GridState n)
    (p : Fin n × Fin n) :
    p ∈ (x.relabelColumns κ).pointSet ↔ (κ.symm p.1, p.2) ∈ x.pointSet := by
  simp

/-- Swapping two rows in a grid state. -/
def swapRows (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid state. -/
def swapColumns (a b : Fin n) (x : GridState n) : GridState n :=
  x.relabelColumns (Equiv.swap a b)

/-- Row swaps evaluate by swapping the row selected by the old state. -/
@[simp]
theorem swapRows_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapRows a b c = Equiv.swap a b (x c) :=
  rfl

/-- Column swaps evaluate by reading the old state at the swapped column. -/
@[simp]
theorem swapColumns_apply (a b : Fin n) (x : GridState n) (c : Fin n) :
    x.swapColumns a b c = x (Equiv.swap a b c) := by
  simp [swapColumns, relabelColumns]

/-- Swapping the same row twice is the identity on grid states. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (x : GridState n) :
    (x.swapRows a b).swapRows a b = x := by
  ext c
  simp [swapRows]

/-- Swapping the same column twice is the identity on grid states. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (x : GridState n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp [swapColumns]

end GridState

namespace GridDiagram

variable {n : ℕ}

/-- Relabel the rows of a grid diagram by relabeling both marking states. -/
def relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelRows ρ
  X := G.X.relabelRows ρ
  disjoint := by
    intro c h
    exact G.disjoint c (ρ.injective h)

/-- Relabel the columns of a grid diagram by relabeling both marking states. -/
def relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) : GridDiagram n where
  O := G.O.relabelColumns κ
  X := G.X.relabelColumns κ
  disjoint := by
    intro c h
    exact G.disjoint (κ.symm c) h

/-- The `O` marking state of a row-relabeled grid diagram. -/
@[simp]
theorem relabelRows_O (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) :
    (G.relabelRows ρ).O = G.O.relabelRows ρ :=
  rfl

/-- The `X` marking state of a row-relabelled grid diagram. -/
@[simp]
theorem relabelRows_X (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) :
    (G.relabelRows ρ).X = G.X.relabelRows ρ :=
  rfl

/-- The `O` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_O (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) :
    (G.relabelColumns κ).O = G.O.relabelColumns κ :=
  rfl

/-- The `X` marking state of a column-relabelled grid diagram. -/
@[simp]
theorem relabelColumns_X (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) :
    (G.relabelColumns κ).X = G.X.relabelColumns κ :=
  rfl

/-- Row relabeling evaluates on the `O` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_O_apply (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) (c : Fin n) :
    (G.relabelRows ρ).O c = ρ (G.O c) :=
  rfl

/-- Row relabeling evaluates on the `X` marking by applying the row permutation. -/
@[simp]
theorem relabelRows_X_apply (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n) (c : Fin n) :
    (G.relabelRows ρ).X c = ρ (G.X c) :=
  rfl

/-- Column relabeling evaluates on the `O` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_O_apply (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) (c : Fin n) :
    (G.relabelColumns κ).O c = G.O (κ.symm c) :=
  rfl

/-- Column relabeling evaluates on the `X` marking at the inverse old column. -/
@[simp]
theorem relabelColumns_X_apply (κ : Equiv.Perm (Fin n)) (G : GridDiagram n) (c : Fin n) :
    (G.relabelColumns κ).X c = G.X (κ.symm c) :=
  rfl

/-- Row relabeling transports the `O` marking set by the row permutation. -/
@[simp]
theorem mem_OSet_relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n)
    (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).OSet ↔ (p.1, ρ.symm p.2) ∈ G.OSet := by
  rw [OSet, OSet]
  exact GridState.mem_pointSet_relabelRows ρ G.O p

/-- Row relabeling transports the `X` marking set by the row permutation. -/
@[simp]
theorem mem_XSet_relabelRows (ρ : Equiv.Perm (Fin n)) (G : GridDiagram n)
    (p : Fin n × Fin n) :
    p ∈ (G.relabelRows ρ).XSet ↔ (p.1, ρ.symm p.2) ∈ G.XSet := by
  rw [XSet, XSet]
  exact GridState.mem_pointSet_relabelRows ρ G.X p

/-- Column relabeling transports the `O` marking set by the column permutation. -/
@[simp]
theorem mem_OSet_relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n)
    (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).OSet ↔ (κ.symm p.1, p.2) ∈ G.OSet := by
  simp [OSet]

/-- Column relabeling transports the `X` marking set by the column permutation. -/
@[simp]
theorem mem_XSet_relabelColumns (κ : Equiv.Perm (Fin n)) (G : GridDiagram n)
    (p : Fin n × Fin n) :
    p ∈ (G.relabelColumns κ).XSet ↔ (κ.symm p.1, p.2) ∈ G.XSet := by
  simp [XSet]

/-- Relabeling rows by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelRows_refl (G : GridDiagram n) : G.relabelRows (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Relabeling columns by the identity permutation does not change a grid diagram. -/
@[simp]
theorem relabelColumns_refl (G : GridDiagram n) :
    G.relabelColumns (Equiv.refl (Fin n)) = G := by
  ext c <;> simp

/-- Swapping two rows in a grid diagram. -/
def swapRows (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelRows (Equiv.swap a b)

/-- Swapping two columns in a grid diagram. -/
def swapColumns (a b : Fin n) (G : GridDiagram n) : GridDiagram n :=
  G.relabelColumns (Equiv.swap a b)

/-- The `O` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_O (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).O = G.O.swapRows a b :=
  rfl

/-- The `X` marking state of a row-swapped grid diagram. -/
@[simp]
theorem swapRows_X (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).X = G.X.swapRows a b :=
  rfl

/-- The `O` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_O (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).O = G.O.swapColumns a b :=
  rfl

/-- The `X` marking state of a column-swapped grid diagram. -/
@[simp]
theorem swapColumns_X (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).X = G.X.swapColumns a b :=
  rfl

/-- Swapping the same pair of rows twice is the identity on grid diagrams. -/
@[simp]
theorem swapRows_swapRows (a b : Fin n) (G : GridDiagram n) :
    (G.swapRows a b).swapRows a b = G := by
  ext c <;> simp [swapRows]

/-- Swapping the same pair of columns twice is the identity on grid diagrams. -/
@[simp]
theorem swapColumns_swapColumns (a b : Fin n) (G : GridDiagram n) :
    (G.swapColumns a b).swapColumns a b = G := by
  ext c <;> simp [swapColumns]

end GridDiagram

end TauCeti
