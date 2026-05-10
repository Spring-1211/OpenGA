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

## Metric access

A `[RiemannianManifold M]` carries the metric as a regular field
`(metric : RiemannianMetric modelI M)` — `RiemannianMetric` is now
Mathlib's `Bundle.ContMDiffRiemannianMetric` aliased, i.e. data, not a
typeclass. Operators access `(RiemannianManifold.metric).metricInner x V W`
or use polymorphic notation that pulls the metric from the typeclass.

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
`(E, H, modelI)` plus the complete typeclass cascade needed by
Riemannian-geometry operators in this framework.

Once `[SmoothManifold M]` is in scope, *all* of the following
synthesize automatically:

* `NormedAddCommGroup E`, `NormedSpace ℝ E`
* `FiniteDimensional ℝ E`, `CompleteSpace E`
* `TopologicalSpace H`
* `ChartedSpace H M`, `IsManifold modelI ∞ M`
* `IsLocallyConstantChartedSpace H M`

A pure-math user reading `[SmoothManifold M]` reads "M is a smooth
finite-dimensional manifold" — exactly the textbook setting. -/
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  /-- The model fibre. -/
  E : Type*
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℝ E]
  [finiteDimensional_E : FiniteDimensional ℝ E]
  [completeSpace_E : CompleteSpace E]
  /-- The model chart codomain. -/
  H : Type*
  [topologicalSpace_H : TopologicalSpace H]
  /-- The model with corners specifying $M$'s smooth structure. -/
  modelI : ModelWithCorners ℝ E H
  [chartedSpace_M : ChartedSpace H M]
  [isManifold_M : IsManifold modelI ∞ M]
  [isLocallyConstantChartedSpace_M : IsLocallyConstantChartedSpace H M]

/-- A **Riemannian manifold** $(M, g)$ as a single bundled typeclass.
Extends `SmoothManifold M` with a regular field
`metric : RiemannianMetric modelI M` (the metric is *data*, an inhabitant
of `Bundle.ContMDiffRiemannianMetric`, not a typeclass attribute).

Bundles `[InnerProductSpace ℝ E]` (needed for chart-background fibre
instances) and `[NeZero (Module.finrank ℝ E)]` (needed for Frobenius
norm / basis sums in curvature / Hessian operators). With these, the
full cascade required by Bochner, Lichnerowicz, second-variation, etc.
is provided by `[RiemannianManifold M]` alone. -/
class RiemannianManifold (M : Type*) [TopologicalSpace M]
    extends SmoothManifold M where
  [innerProductSpace_E : InnerProductSpace ℝ E]
  [neZero_finrank_E : NeZero (Module.finrank ℝ E)]
  /-- The metric on $M$, attached to the inherited `modelI`. -/
  metric : RiemannianMetric modelI M

end OpenGALib
