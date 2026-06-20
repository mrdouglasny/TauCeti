/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homeomorph.Defs
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient

/-!
# The orbit quotient of a regular covering map is homeomorphic to the base

For a regular deck action, `Deck.IsRegular.orbitQuotientEquivBase` already identifies the
deck-orbit quotient `E / Deck p` with the base `B` as a bare equivalence. This file upgrades
that equivalence to a homeomorphism when `p` is a covering map: the orbit-quotient projection
carries the quotient topology, the induced map to the base is continuous because it lifts the
covering projection, and it is open because a covering projection is an open map and the
orbit-quotient projection is surjective.

This is the abstract form of the universal-covers identity `UniversalCover x₀ / π₁(X, x₀) ≃ X`,
stated for an arbitrary regular covering map rather than the specific based-path cover. Only
`IsCoveringMap p` and `Deck.IsRegular p` are needed; the total space is not assumed
preconnected.

## Main declarations

* `TauCeti.Deck.continuous_orbitQuotientToBase`: the map `E / Deck p → B` induced by a
  covering projection is continuous.
* `TauCeti.Deck.isOpenMap_orbitQuotientToBase`: that map is open.
* `TauCeti.Deck.IsRegular.orbitQuotientHomeomorphBase`: for a regular covering map,
  `E / Deck p` is homeomorphic to the base.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 1, where
`UniversalCover x₀ / π₁(X, x₀) ≃ X` follows from the deck-group identification via Mathlib's
`IsQuotientCoveringMap`; the present statement is its base-independent regular-cover form.
-/

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- The map from the deck-orbit quotient to the base, induced by a covering projection, is
continuous: it lifts the (continuous) projection through the quotient topology. -/
lemma continuous_orbitQuotientToBase (hp : IsCoveringMap p) :
    Continuous (orbitQuotientToBase p) :=
  hp.continuous.quotient_lift fun _ _ h => eq_proj_of_orbitRel h

/-- The map from the deck-orbit quotient to the base, induced by a covering projection, is an
open map. The orbit-quotient projection `Quotient.mk''` is surjective and the projection `p`
factors through it, so the image of an open set is the `p`-image of an open set, hence open
because a covering projection is an open map. -/
lemma isOpenMap_orbitQuotientToBase (hp : IsCoveringMap p) :
    IsOpenMap (orbitQuotientToBase p) := by
  intro V hV
  have hsurj : Function.Surjective
      (Quotient.mk'' : E → MulAction.orbitRel.Quotient (Deck p) E) :=
    Quotient.mk''_surjective
  have hpre : IsOpen ((Quotient.mk'' : E → MulAction.orbitRel.Quotient (Deck p) E) ⁻¹' V) :=
    hV.preimage continuous_quotient_mk'
  have himg : orbitQuotientToBase p '' V =
      p '' ((Quotient.mk'' : E → MulAction.orbitRel.Quotient (Deck p) E) ⁻¹' V) := by
    ext b
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hxV, rfl⟩
      obtain ⟨e, rfl⟩ := hsurj x
      exact ⟨e, hxV, rfl⟩
    · rintro ⟨e, heV, rfl⟩
      exact ⟨Quotient.mk'' e, heV, rfl⟩
  rw [himg]
  exact hp.isOpenMap _ hpre

namespace IsRegular

/-- For a regular covering map, the deck-orbit quotient `E / Deck p` is homeomorphic to the
base. This upgrades `Deck.IsRegular.orbitQuotientEquivBase` from an equivalence to a
homeomorphism, using that a covering projection is continuous and open. -/
noncomputable def orbitQuotientHomeomorphBase (hreg : IsRegular p) (hp : IsCoveringMap p) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ₜ B :=
  hreg.orbitQuotientEquivBase.toHomeomorphOfContinuousOpen
    (continuous_orbitQuotientToBase hp) (isOpenMap_orbitQuotientToBase hp)

/-- On the underlying equivalence, the orbit-quotient homeomorphism is
`orbitQuotientEquivBase`. -/
@[simp]
lemma orbitQuotientHomeomorphBase_apply (hreg : IsRegular p) (hp : IsCoveringMap p)
    (x : MulAction.orbitRel.Quotient (Deck p) E) :
    hreg.orbitQuotientHomeomorphBase hp x = hreg.orbitQuotientEquivBase x :=
  rfl

/-- The orbit-quotient homeomorphism evaluates on representatives by the projection map. -/
@[simp]
lemma orbitQuotientHomeomorphBase_mk (hreg : IsRegular p) (hp : IsCoveringMap p) (e : E) :
    hreg.orbitQuotientHomeomorphBase hp
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e :=
  rfl

/-- The inverse orbit-quotient homeomorphism sends a projected point to the class of any
lift. -/
@[simp]
lemma orbitQuotientHomeomorphBase_symm_apply_proj (hreg : IsRegular p) (hp : IsCoveringMap p)
    (e : E) :
    (hreg.orbitQuotientHomeomorphBase hp).symm (p e) =
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) :=
  hreg.orbitQuotientEquivBase_symm_apply_proj e

end IsRegular

end Deck

end TauCeti
