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

open Bundle
open scoped ContDiff Manifold Bundle

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

/-! ## Global instance bridges

Class fields tagged `[...]` are accessible to type-class search only via
parent-chain projection from `[SmoothManifold M]` / `[RiemannianManifold
M]`. Lean's TC engine can occasionally fail to chain these projections at
the right elaboration sites (especially when the projected type appears
under an `outParam` like `E` here). The bridges below promote each
instance field to a top-level instance so synthesis is direct. -/

section SmoothManifoldBridges

variable {M : Type*} [TopologicalSpace M] [s : SmoothManifold M]

instance : NormedAddCommGroup s.E := s.normedAddCommGroup_E
instance : NormedSpace ℝ s.E := s.normedSpace_E
instance : FiniteDimensional ℝ s.E := s.finiteDimensional_E
instance : CompleteSpace s.E := s.completeSpace_E
instance : TopologicalSpace s.H := s.topologicalSpace_H
instance : ChartedSpace s.H M := s.chartedSpace_M
instance : IsManifold s.modelI ∞ M := s.isManifold_M
instance : IsLocallyConstantChartedSpace s.H M := s.isLocallyConstantChartedSpace_M

end SmoothManifoldBridges

section RiemannianManifoldBridges

variable {M : Type*} [TopologicalSpace M] [rm : RiemannianManifold M]

instance : InnerProductSpace ℝ rm.E := rm.innerProductSpace_E
instance : NeZero (Module.finrank ℝ rm.E) := rm.neZero_finrank_E

/-- The metric carried by `[RiemannianManifold M]` induces a global
`Bundle.RiemannianBundle (TangentSpace modelI : M → Type _)`, which in turn
activates Mathlib's scoped `NormedAddCommGroup` and `InnerProductSpace ℝ`
instances on each fibre `TangentSpace modelI x`. This is the single
NACG/IPS source on tangent fibres in OpenGALib — chart-background
shortcuts (`inferInstanceAs (NormedAddCommGroup E)` on `TangentSpace I x`)
were deliberately retired in favour of this bridge, sidestepping the
lean4#13063 NACG diamond. -/
noncomputable instance instRiemannianBundleOfRiemannianManifold :
    Bundle.RiemannianBundle (TangentSpace rm.modelI : M → Type _) :=
  ⟨rm.metric.toRiemannianMetric⟩

end RiemannianManifoldBridges

end OpenGALib
