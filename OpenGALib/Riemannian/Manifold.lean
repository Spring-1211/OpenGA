import OpenGALib.Riemannian.Metric

/-!
# Smooth and Riemannian manifolds — bundled typeclass

A pure-math user reasons about a Riemannian manifold as the data
$(M, g)$. The Mathlib machinery $(E, H, I, \text{ChartedSpace}, \text{IsManifold})$
is implementation detail, invisible at the math layer. The typeclasses
in this file expose that layering directly:

  * `[SmoothManifold M]` — bundles $(E, H, I)$ + chart machinery + smooth
    structure. One typeclass parameter replaces five.
  * `[RiemannianManifold M]` — extends `[SmoothManifold M]` with a
    Riemannian metric. One typeclass parameter replaces six.

Operators downstream (`metricInner`, `manifoldGradient`, `Δ_g`, `Ric`,
...) take `[RiemannianManifold M]` and recover everything they need.

## Why bundle

* **Math-first surface**: `class RiemannianManifold M` reads "M is a
  Riemannian manifold" — the same sentence a textbook opens with.
  Notation built on it (`‖∇f‖²_g`, `Δ_g f`, `Ric(X, Y)`) carries no
  Lean-machinery sub/superscripts.
* **AI-co-governance**: typeclass synthesis cannot stick on `M ↛ I`
  (the issue that forced `[I]`-bracket workarounds elsewhere).
  `[RiemannianManifold M]` makes `M` determine all the data.
* **Extension contract**: new geometric structures (Lorentzian, Kähler,
  symplectic, contact) extend `SmoothManifold M` the same way; the
  framework's typeclass family is uniform.

## Backward compatibility

A `[RiemannianManifold M]` provides a `[RiemannianMetric I M]` instance
via `RiemannianManifold.toRiemannianMetric`. All existing operators
written against `RiemannianMetric I M` work unchanged when the user
declares `[RiemannianManifold M]`.

## Extension policy

To add a new geometric structure on smooth manifolds:

1. `class XManifold (M : Type*) [TopologicalSpace M] extends SmoothManifold M where ...`
2. Bundle the structural data fields (e.g. `pseudoMetric` for
   Lorentzian, `complexStructure` for almost-complex/Kähler).
3. Provide bridge instances to existing structure-specific typeclasses
   if the new structure is a refinement (e.g. Kähler → Riemannian).
4. Document in `docs/RIEMANNIAN_FRAMEWORK_SPEC.md` (the spec lists all
   manifold typeclasses in the framework and their bridges).

**Ground truth**: do Carmo, *Riemannian Geometry*, §1.1 ("Riemannian
manifolds and Riemannian metrics"). Lee, *Smooth Manifolds*, Ch. 1, 13.
-/

open scoped ContDiff Manifold

namespace OpenGALib

/-- A **smooth manifold** as a single bundled typeclass. Packages
`(E, H, modelI)` plus the standard typeclass cascade required to talk
about smooth functions on $M$.

Once `[SmoothManifold M]` is in scope, all of
`NormedAddCommGroup E`, `NormedSpace ℝ E`, `TopologicalSpace H`,
`ChartedSpace H M`, `IsManifold modelI ∞ M` are also available via
typeclass synthesis. -/
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  /-- The model fibre. -/
  E : Type*
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℝ E]
  /-- The model chart codomain. -/
  H : Type*
  [topologicalSpace_H : TopologicalSpace H]
  /-- The model with corners specifying $M$'s smooth structure. -/
  modelI : ModelWithCorners ℝ E H
  [chartedSpace_M : ChartedSpace H M]
  [isManifold_M : IsManifold modelI ∞ M]

/-- A **Riemannian manifold** $(M, g)$ as a single bundled typeclass.
Extends `SmoothManifold M` with a `RiemannianMetric` instance for
$M$'s smooth structure. -/
class RiemannianManifold (M : Type*) [TopologicalSpace M]
    extends SmoothManifold M where
  /-- The metric on $M$, attached to the inherited `modelI`. -/
  [toRiemannianMetric : RiemannianMetric modelI M]

end OpenGALib
