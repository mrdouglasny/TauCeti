/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homotopy.Lifting

/-!
# The monodromy action on a fibre

Mathlib's covering-space API associates to a covering map `p : E → X` a monodromy functor
from the fundamental groupoid of `X` to types. This file packages the restriction of that
functor to a based loop as a permutation of the fibre over the basepoint, then records the
corresponding action of `π₁(X, x)` on that fibre.

This is a small prerequisite for the universal-covers roadmap: Stage 1 asks to pin the
composition convention in the comparison between deck transformations and the fundamental
group, and Stage 2 proposes the classification of connected covers through transitive
`π₁`-sets and Mathlib's `monodromyFunctor`.
-/

namespace TauCeti

open FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The identity element of the fundamental group is represented by the constant path. -/
lemma fundamentalGroup_toPath_one :
    (1 : FundamentalGroup X x).toPath = Path.Homotopic.Quotient.refl x :=
  by
    -- `FundamentalGroup.toPath` is the endomorphism hom coerced through
    -- `End.asHom`; Mathlib has no named `toPath_one` lemma, so expose that
    -- definitional bridge before using the categorical identity lemma.
    change CategoryTheory.End.asHom
      (1 : CategoryTheory.End (FundamentalGroupoid.mk x)) =
      Path.Homotopic.Quotient.refl x
    rw [CategoryTheory.End.one_def, FundamentalGroupoid.id_eq_path_refl]
    -- The previous rewrite leaves the raw quotient constructor, while
    -- `Path.Homotopic.Quotient.refl` is a wrapper around the same class.
    change Path.Homotopic.Quotient.mk (Path.refl x) = Path.Homotopic.Quotient.refl x
    rw [Path.Homotopic.Quotient.mk_refl]

/-- Mathlib's multiplication convention for fundamental-group loops as path homotopy classes.

The fundamental group is the endomorphism group of a fundamental-groupoid object, so
multiplication follows categorical endomorphism multiplication. On path homotopy classes this
means `γ * δ` is represented by first traversing `δ`, then `γ`. -/
lemma fundamentalGroup_toPath_mul (γ δ : FundamentalGroup X x) :
    (γ * δ).toPath = Path.Homotopic.Quotient.trans δ.toPath γ.toPath :=
  by
    -- There is no named Mathlib lemma bridging `(γ * δ).toPath` to
    -- endomorphism multiplication, so first expose the underlying hom in the
    -- fundamental groupoid and then use the named category/path lemmas below.
    change (γ * δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) =
      Path.Homotopic.Quotient.trans δ.toPath γ.toPath
    calc
      (γ * δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x)
          = CategoryTheory.CategoryStruct.comp
              (δ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x)
              (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) := by
            exact CategoryTheory.End.mul_def
              (xs := (γ : CategoryTheory.End (FundamentalGroupoid.mk x)))
              (ys := (δ : CategoryTheory.End (FundamentalGroupoid.mk x)))
      _ = Path.Homotopic.Quotient.trans δ.toPath γ.toPath := by
            rw [FundamentalGroupoid.comp_eq]

/-- The map on fundamental groups is represented by mapping the underlying path homotopy class. -/
lemma fundamentalGroup_map_toPath {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    (γ : FundamentalGroup X x) :
    (map f x γ).toPath = γ.toPath.map f :=
  FundamentalGroup.map_apply f x γ

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
variable (cov : IsCoveringMap p) (x : X)

/-- The monodromy of a based loop, as a permutation of the fibre over the basepoint. -/
noncomputable def monodromyPerm (γ : FundamentalGroup X x) : Equiv.Perm (p ⁻¹' {x}) :=
  Equiv.ofBijective (cov.monodromy γ.toPath) (cov.monodromy_bijective γ.toPath)

/-- The monodromy permutation is Mathlib's monodromy map on points of the fibre. -/
@[simp]
lemma monodromyPerm_apply (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    monodromyPerm cov x γ e = cov.monodromy γ.toPath e :=
  rfl

/-- The identity loop acts by the identity permutation of the fibre. -/
@[simp]
lemma monodromyPerm_one : monodromyPerm cov x 1 = 1 := by
  ext e
  rw [monodromyPerm_apply, fundamentalGroup_toPath_one]
  exact congr_arg Subtype.val (congr_fun cov.monodromy_refl e)

/-- Monodromy is compatible with the multiplication convention on Mathlib's fundamental group.

The fundamental group is the endomorphism group of the basepoint in the fundamental groupoid;
its multiplication is the endomorphism multiplication from category theory. With that
convention, monodromy is a monoid homomorphism to permutations of the fibre. -/
@[simp]
lemma monodromyPerm_mul (γ δ : FundamentalGroup X x) :
    monodromyPerm cov x (γ * δ) = monodromyPerm cov x γ * monodromyPerm cov x δ := by
  ext e
  rw [monodromyPerm_apply, fundamentalGroup_toPath_mul]
  exact congr_arg Subtype.val (cov.monodromy_trans_apply δ.toPath γ.toPath e)

/-- The inverse loop acts by the inverse monodromy permutation. -/
@[simp]
lemma monodromyPerm_inv (γ : FundamentalGroup X x) :
    monodromyPerm cov x γ⁻¹ = (monodromyPerm cov x γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← monodromyPerm_mul, inv_mul_cancel, monodromyPerm_one]

/-- The monodromy representation of the fundamental group on the fibre over the basepoint. -/
noncomputable def monodromyPermHom : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x}) where
  toFun := monodromyPerm cov x
  map_one' := monodromyPerm_one cov x
  map_mul' := monodromyPerm_mul cov x

/-- The monodromy homomorphism evaluates to the monodromy permutation. -/
@[simp]
lemma monodromyPermHom_apply (γ : FundamentalGroup X x) :
    monodromyPermHom cov x γ = monodromyPerm cov x γ :=
  rfl

/-- A covering map's fundamental group action on a fibre by monodromy.

Use this locally with `letI := cov.monodromyMulAction x` when treating the fibre as a
`π₁(X, x)`-set. It is a named definition rather than a global instance because the covering-map
proof `cov` is not inferable from the action type. -/
@[reducible]
noncomputable def monodromyMulAction : MulAction (FundamentalGroup X x) (p ⁻¹' {x}) :=
  MulAction.compHom _ (monodromyPermHom cov x)

/-- On points, the monodromy action is Mathlib's monodromy map. -/
lemma monodromy_smul_eq (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    letI := monodromyMulAction cov x
    γ • e = cov.monodromy γ.toPath e :=
  rfl

/-- The monodromy action agrees with the monodromy permutation. -/
lemma monodromy_smul_eq_monodromyPerm (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    letI := monodromyMulAction cov x
    γ • e = monodromyPerm cov x γ e :=
  rfl

/-- If a loop in the total space projects to a loop in the base, its monodromy fixes the
starting point in the fibre. -/
@[simp]
lemma monodromyPerm_map_self (e : E) (γ : FundamentalGroup E e) :
    monodromyPerm cov (p e) (map ⟨p, cov.continuous⟩ e γ) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  rw [monodromyPerm_apply, fundamentalGroup_map_toPath]
  exact cov.monodromy_map γ.toPath

/-- The monodromy action fixes the starting point of a lifted loop. -/
lemma map_smul_self (e : E) (γ : FundamentalGroup E e) :
    letI := monodromyMulAction cov (p e)
    map ⟨p, cov.continuous⟩ e γ • (⟨e, by simp⟩ : p ⁻¹' {p e}) = ⟨e, by simp⟩ :=
  monodromyPerm_map_self cov e γ

/-- A projected loop from the total space fixes its starting point under monodromy. -/
lemma smul_eq_self_of_mem_map_range (e : E) {γ : FundamentalGroup X (p e)}
    (hγ : γ ∈ (map ⟨p, cov.continuous⟩ e).range) :
    letI := monodromyMulAction cov (p e)
    γ • (⟨e, by simp⟩ : p ⁻¹' {p e}) = ⟨e, by simp⟩ := by
  rcases hγ with ⟨δ, rfl⟩
  exact map_smul_self cov e δ

/-- The image of the fundamental group of the total space is contained in the stabilizer of the
chosen point in the fibre under the monodromy action. -/
lemma map_range_le_stabilizer (e : E) :
    letI := monodromyMulAction cov (p e)
    (map ⟨p, cov.continuous⟩ e).range ≤
      MulAction.stabilizer (FundamentalGroup X (p e)) (⟨e, by simp⟩ : p ⁻¹' {p e}) := by
  intro γ hγ
  letI := monodromyMulAction cov (p e)
  exact MulAction.mem_stabilizer_iff.mpr (smul_eq_self_of_mem_map_range cov e hγ)

end IsCoveringMap

end TauCeti
