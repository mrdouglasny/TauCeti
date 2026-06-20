/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.NumberTheory.Multiquadratic.Degree
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Squarefree

/-!
# Multiquadratic fields with prime radicands

The field-generic degree theorem `TauCeti.Multiquadratic.finrank_adjoin_range` says that a
multiquadratic field has degree `2ⁿ` once the radicands are **square-class independent**: no
nonempty subset product of them is a square. This file supplies that hypothesis for the most
common concrete source of square-class independent radicands — a family of **distinct primes** —
and so derives the prime-indexed degree corollary `[ℚ(√p₁, …, √pₙ) : ℚ] = 2ⁿ` (a genus-theory
input) and the smallest non-vacuity example `[ℚ(√2, √3) : ℚ] = 4`.

The square-class independence of distinct primes is elementary: a nonempty subset product of
distinct primes is squarefree (the primes are pairwise coprime) and is not a unit (it has a prime
factor), so it is not a square.

## Main results

* `TauCeti.Multiquadratic.not_isSquare_of_squarefree`: a squarefree non-unit is not a square.
* `TauCeti.Multiquadratic.not_isSquare_prod_primes`: for distinct primes `p i`, no nonempty subset
  product `∏_{i ∈ S} (p i : ℚ)` is a square — square-class independence in the form the degree
  theorem consumes.
* `TauCeti.Multiquadratic.finrank_adjoin_sqrt_primes`: `[ℚ(√p₁, …, √pₙ) : ℚ] = 2^|ι|` for a finite
  family of distinct primes.
* `TauCeti.Multiquadratic.finrank_adjoin_sqrt_two_three`: `[ℚ(√2, √3) : ℚ] = 4`.
-/

open scoped Function

namespace TauCeti.Multiquadratic

/-- A squarefree non-unit is not a square: if `a = r * r` then `r * r ∣ a` forces `r` to be a unit,
hence `a` a unit. -/
theorem not_isSquare_of_squarefree {R : Type*} [CommMonoid R] {a : R}
    (ha : Squarefree a) (hu : ¬ IsUnit a) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  exact hu ((ha r dvd_rfl).mul (ha r dvd_rfl))

/-- **Square-class independence of distinct primes.** If the `p i` are prime and pairwise distinct,
then no nonempty subset product `∏_{i ∈ S} (p i : ℚ)` is a square in `ℚ`. This is the hypothesis the
multiquadratic degree theorem `finrank_adjoin_range` consumes. -/
theorem not_isSquare_prod_primes {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {S : Finset ι} (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (p i : ℚ)) := by
  rw [← Nat.cast_prod, Rat.isSquare_natCast_iff]
  refine not_isSquare_of_squarefree ?_ ?_
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun i _ j _ hij => ?_)
      (fun i _ => (hp i).prime.squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp i) (hp j)).mpr fun h => hij (hinj h))
  · rw [Nat.isUnit_iff]
    obtain ⟨i, hi⟩ := hS
    intro hprod
    exact (hp i).ne_one (Nat.dvd_one.mp (hprod ▸ Finset.dvd_prod_of_mem p hi))

/-- **Degree of a prime-radicand multiquadratic field.** For a finite family of distinct primes
`p : ι → ℕ`, the field generated over `ℚ` by their real square roots has degree `2^|ι|`. This is the
prime-indexed corollary of the field-generic degree theorem `finrank_adjoin_range`. -/
theorem finrank_adjoin_sqrt_primes {ι : Type*} [Finite ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Module.finrank ℚ
        (IntermediateField.adjoin ℚ (Set.range fun i => (Real.sqrt (p i) : ℝ)))
      = 2 ^ Nat.card ι := by
  refine finrank_adjoin_range (d := fun i => (p i : ℚ))
    (root := fun i => Real.sqrt (p i)) (fun i => ?_) (fun S hS => ?_)
  · rw [Real.sq_sqrt (Nat.cast_nonneg _), map_natCast]
  · exact not_isSquare_prod_primes p hp hinj hS

/-- **Worked example: `[ℚ(√2, √3) : ℚ] = 4`.** The smallest nontrivial multiquadratic degree,
obtained from `finrank_adjoin_sqrt_primes` with the primes `2` and `3`. -/
theorem finrank_adjoin_sqrt_two_three :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ {Real.sqrt 2, Real.sqrt 3} : IntermediateField ℚ ℝ) = 4 := by
  have h := finrank_adjoin_sqrt_primes ![2, 3] (by decide) (by decide)
  have hset : (Set.range fun i : Fin 2 => Real.sqrt ((![2, 3] : Fin 2 → ℕ) i))
      = {Real.sqrt 2, Real.sqrt 3} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hset] at h
  rw [h]
  simp

end TauCeti.Multiquadratic
