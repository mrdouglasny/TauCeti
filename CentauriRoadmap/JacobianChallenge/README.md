# Roadmap: the Jacobian challenge (Christian Merten's AG version)

Background: Kevin Buzzard's "Jacobian challenge" (Zulip
[#Autoformalization > Jacobian challenge](https://leanprover.zulipchat.com/#narrow/channel/417987-Autoformalization/topic/Jacobian.20challenge)).
The challenge is deliberately designed with **checks along the way** so that any
construction that satisfies them all has to have got the definitions right — the
point is autoformalizing *definitions*, not just discharging `sorry`s. There are two
flavours: a differential-geometry version (compact Riemann surfaces) and the
**algebraic-geometry version due to Christian Merten**, which is the target here.

## Target (v1)

Construct the **Jacobian of a smooth, proper, geometrically connected curve `X` over
a field `k` that has a `k`-rational point**, as `Pic⁰(X)`: an abelian variety —
equivalently a finite-type group scheme over `k` — characterized by its **universal
property** via the Abel–Jacobi map, and **compatible with base change**.

In the AG version, compatibility between independently-produced solutions is
*automatic*: the universal property supplies the comparison isomorphism (Christian
Merten). So we phrase the target as a universal property rather than a bare
construction.

```lean
-- Schematic shape (promote to compiled `sorry` targets once the scheme-level
-- Picard / abelian-variety API in the pin supports it):

-- X : smooth proper geometrically-connected curve over k, with a chosen k-point x₀.
-- noncomputable def Jacobian : AbelianVariety k := sorry   -- = Pic⁰ X

-- Abel–Jacobi: X → Jacobian sending x₀ ↦ 0, initial among pointed maps to
-- abelian varieties:
-- def abelJacobi : X ⟶ (Jacobian).toScheme := sorry
-- theorem abelJacobi_universal : <initial among pointed maps X → A, A abelian> := sorry

-- Compatible with base change along k → K:
-- theorem jacobian_baseChange : (Jacobian).baseChange K ≅ Jacobian (X.baseChange K) := sorry
```

## Acceptance criteria ("checks along the way")

Following Kevin's design principle (e.g. in the diff-geom version,
`genus X = 0 ↔ Nonempty (X ≃ₜ sphere)`), a finished construction must satisfy
sanity checks that rule out vacuous definitions, for example:

- `dim Jacobian = genus X`;
- `Jacobian` of an elliptic curve `(E, O)` is `E` itself (with its group law);
- the Abel–Jacobi map is a closed immersion for `genus X ≥ 1`;
- base-change compatibility above.

## Scope and caveats (Kevin Buzzard)

- **`k`-rational point is assumed.** The no-point case is a different object — the
  Albanese torsor / `Pic¹` — and is **out of scope for v1**. (Christian Merten: the
  curve admits a map to `Pic¹` rather than `Pic⁰`.)
- **Jacobian ≠ Albanese in general.** They are canonically isomorphic in good cases
  but have *opposite* functorialities (`Pic⁰` is contravariant; the Albanese is
  covariant, universal for maps from the pointed curve to abelian varieties). The
  Abel–Jacobi map gives the contravariant object the universal property of the
  covariant one. Keep the two distinct if/when v2 drops the `k`-point hypothesis.

## Prerequisites

Scheme-level Picard functor, abelian varieties / proper group schemes over a field,
and the curve API (genus, smoothness, properness) at the pinned Mathlib commit.
Several of these are still developing upstream; promote the sketch above into
compiled `Targets.lean` declarations as the pin advances.
