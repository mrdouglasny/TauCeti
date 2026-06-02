# Roadmap: the Jacobian challenge (Christian Merten's AG version)

Background: Kevin Buzzard's "Jacobian challenge" (Zulip
[#Autoformalization > Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/417987-Autoformalization/topic/Jacobian.20challenge)),
in the **algebraic-geometry formulation due to Christian Merten**. The challenge is
designed with **checks along the way**, so a construction that satisfies them all has
to have the definitions right — the point is autoformalizing *definitions*, not just
discharging `sorry`s.

**We are not waiting for Mathlib.** Almost none of the prerequisite stack (Picard
functor, sheaf cohomology to the depth needed, abelian varieties) is in Mathlib, and
it will not arrive on any schedule we can plan around. So this is a roadmap to **build
the entire prerequisite tower here**, in `Centauri/`, iteratively — each layer is real
sorry-free mathematics that the next layer builds on. Suggested home:
`Centauri/AlgebraicGeometry/Jacobian/` with the supporting theories under
`Centauri/AlgebraicGeometry/`.

## The end goal (v1)

For a **smooth, proper, geometrically connected curve `X` over a field `k` with a
`k`-rational point `x₀`**, construct the **Jacobian** `Jac X = Pic⁰(X)` as an abelian
variety over `k`, characterized by the universal property of the Abel–Jacobi map and
compatible with base change.

```lean
-- the shape we are building toward (state in Targets.lean as the types appear):
-- noncomputable def Jacobian (X : Curve k) (x₀ : X.point) : AbelianVariety k
-- def abelJacobi : X ⟶ (Jacobian X x₀).toScheme            -- x₀ ↦ 0
-- theorem abelJacobi_universal : <initial among pointed maps X → A, A abelian>
-- theorem jacobian_baseChange (K : Field) [Algebra k K] :
--     (Jacobian X x₀).baseChange K ≅ Jacobian (X.baseChange K) (x₀.baseChange K)
```

In the AG version, comparison of independently-built solutions is *automatic*: the
universal property supplies the isomorphism (Christian Merten). So the target is phrased
as a universal property, not a bare construction.

## The prerequisite tower (build order)

Each layer is a self-contained body of theory worth having in its own right. Consume
whatever already exists in Mathlib (schemes, morphism properties: proper / smooth /
separated / finite-type, base change); build everything else here.

### Layer A — line bundles, divisors, and the Picard group
- Invertible sheaves on a scheme; the Picard group `Pic X` (iso classes of line bundles
  under `⊗`).
- Weil and Cartier divisors on a curve; the divisor ↔ line-bundle dictionary; the
  `degree` homomorphism `Pic X → ℤ` and `Pic⁰ X = ker degree`.

### Layer B — coherent sheaf cohomology on a curve
- Coherent sheaves; cohomology `Hⁱ(X, ℱ)`; finite-dimensionality for proper `X` over `k`.
- `H⁰`, `H¹` on a curve; the **genus** `g = dimₖ H¹(X, 𝒪_X)`.
- Riemann–Roch and Serre duality for curves (needed for dimension counts and to build
  Abel–Jacobi).

### Layer C — the relative Picard functor and its representability
- The functor `Picᴿᵉˡ_{X/k} : (Sch/k)ᵒᵖ ⥤ Ab`, rigidified by `x₀` (the `k`-point kills
  the `Pic(T)` ambiguity and makes it a sheaf); its subfunctor `Pic⁰`.
- **Representability** — the crux. Represent `Pic⁰_{X/k}` by a `k`-scheme `Jac X`. Two
  routes to evaluate:
  1. *Curve-specific*: symmetric powers `Symᵈ X`, the Abel–Jacobi map from `Symᵍ X`, and
     descent — avoids the general Picard-scheme machinery.
  2. *General*: the Picard scheme of a projective variety, then specialize.
  The roadmap should pursue route 1 first; it is the shortest path to a curve Jacobian.

### Layer D — abelian varieties
- Group schemes over a field (consume the group-object machinery; see the reductive
  groups roadmap, which paves the same `GrpObj`/Hopf-algebra ground); proper + smooth +
  geometrically connected ⇒ **abelian variety**; basic API and `dim`.
- Show `Jac X` is an abelian variety; **`dim (Jac X) = g`**.

### Layer E — Abel–Jacobi and the universal property
- The Abel–Jacobi morphism `aj : X ⟶ Jac X`, `x₀ ↦ 0`.
- Universal property: `aj` is initial among pointed morphisms from `X` to abelian
  varieties (the Albanese property), which yields the comparison isomorphism for free.
- Base-change compatibility along `k → K`.

## Acceptance criteria ("checks along the way")

Following Kevin's design principle (e.g. in the diff-geom version,
`genus X = 0 ↔ Nonempty (X ≃ₜ sphere)`), a finished construction must pass sanity checks
that rule out vacuous definitions:
- `dim (Jac X) = genus X`;
- `Jac` of an elliptic curve `(E, O)` is `E` with its group law;
- `aj` is a closed immersion for `genus X ≥ 1`;
- base-change compatibility above.

## Scope and caveats (Kevin Buzzard)

- **The `k`-rational point is assumed.** The no-point case is a *different* object — the
  Albanese torsor / `Pic¹` — and is **out of scope for v1**. (Merten: the curve maps to
  `Pic¹`, not `Pic⁰`.)
- **Jacobian ≠ Albanese in general.** Canonically isomorphic in good cases but with
  *opposite* functorialities (`Pic⁰` contravariant; Albanese covariant, universal for maps
  from the pointed curve to abelian varieties). The Abel–Jacobi map endows the
  contravariant object with the covariant object's universal property. Keep them distinct
  if v2 drops the `k`-point hypothesis.

## How to drive it

This tower is large by design and meant to be expanded **iteratively**. Build Layer A,
then B, … ; as each layer makes the next layer's *types* expressible, state that layer's
milestones in `Targets.lean` (with `sorry`) and hand them to the AIs to discharge in
`Centauri/`. Nothing here blocks on upstream Mathlib.
