/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Splitting completely and the decomposition group

For a Galois number field `F / ℚ` and a prime `Q` of `𝓞 F` lying above a rational prime `p`, the
prime `p` splits completely — there are exactly `[F : ℚ]` primes of `𝓞 F` above `p` — if and only
if the decomposition group of `Q`, i.e. its stabilizer under the natural action of `Gal(F/ℚ)`, is
trivial.

This is the decomposition-group form of complete splitting, complementing the ramification/inertia
counting criterion. The proof is orbit–stabilizer: `Gal(F/ℚ)` acts on the primes above `p` with a
single orbit (`Algebra.IsInvariant.orbit_eq_primesOver`), so the number of primes is
`[F : ℚ] / |decomposition group|`.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`: complete splitting is
  equivalent to a trivial decomposition group.

## Provenance

Assembled from Mathlib's transitivity of the Galois action on primes
(`Algebra.IsInvariant.orbit_eq_primesOver`) and orbit–stabilizer; prepared for the multiquadratic
prime-splitting law (Layer 1 of the multiquadratic roadmap).
-/

open NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

/-- **Splitting completely ⟺ trivial decomposition group.** For a Galois number field `F` and a
prime `Q` of `𝓞 F` above the rational prime `p`, `p` splits completely (there are `[F : ℚ]` primes
above `p`) iff the decomposition group of `Q` — its stabilizer in `Gal(F/ℚ)` — is trivial. -/
theorem ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot (F : Type*) [Field F]
    [NumberField F] [IsGalois ℚ F] {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    (primesOver (span {(p : ℤ)}) (𝓞 F)).ncard = finrank ℚ F ↔
      stabilizer (F ≃ₐ[ℚ] F) Q = ⊥ := by
  have horbit : orbit (F ≃ₐ[ℚ] F) Q = (span {(p : ℤ)}).primesOver (𝓞 F) :=
    Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 F) (F ≃ₐ[ℚ] F) (span {(p : ℤ)}) Q
  have hkey : (primesOver (span {(p : ℤ)}) (𝓞 F)).ncard *
      Nat.card (stabilizer (F ≃ₐ[ℚ] F) Q) = finrank ℚ F := by
    rw [← Nat.card_coe_set_eq, ← horbit, ← Nat.card_prod,
      Nat.card_congr (orbitProdStabilizerEquivGroup (F ≃ₐ[ℚ] F) Q),
      IsGalois.card_aut_eq_finrank]
  have hpos : 0 < finrank ℚ F := finrank_pos
  constructor
  · intro hn
    rw [hn] at hkey
    exact Subgroup.card_eq_one.mp
      (Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hkey))
  · intro hst
    rw [hst] at hkey
    simpa using hkey

end TauCeti.NumberField
