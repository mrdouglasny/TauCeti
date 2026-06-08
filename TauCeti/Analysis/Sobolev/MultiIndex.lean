/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Weight

/-!
# Multiindices for Sobolev spaces

For the PDE roadmap Lane A, the Sobolev norm on a finite-dimensional domain is indexed by
all finitely supported natural-valued functions of total degree at most `k`. Mathlib already
provides the underlying multiindex representation `ι →₀ ℕ`, coordinate units via
`Finsupp.single`, total degree via `Finsupp.degree`, and bounded-degree finiteness via
`Finsupp.finite_of_degree_le`; this file only gives those bounded Sobolev indexing types
project-local names.
-/

namespace TauCeti

/-- A multiindex on `ι`, represented by Mathlib's finitely supported functions. -/
abbrev MultiIndex (ι : Type*) : Type _ :=
  ι →₀ ℕ

namespace MultiIndex

/-- Multiindices whose total degree is at most `k`, as a subtype. -/
abbrev DegreeLE (ι : Type*) (k : ℕ) : Type _ :=
  { α : MultiIndex ι // Finsupp.degree α ≤ k }

variable {k : ℕ}

noncomputable instance degreeLEFintype [Finite ι] : Fintype (DegreeLE ι k) := by
  classical
  exact Set.Finite.fintype (Finsupp.finite_of_degree_le (σ := ι) k)

end MultiIndex

end TauCeti
