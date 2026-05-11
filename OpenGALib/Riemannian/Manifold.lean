import OpenGALib.Riemannian.Metric
import OpenGALib.Util.Attributes

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

/-! ## Math-first metric API

Downstream operator code reads as textbook math when the metric is
carried implicitly by `[RiemannianManifold M]`:

* `metricInner x v w`           (inner product on `T_xM`, not `g.metricInner`)
* `metricRiesz x φ`             (Riesz dual vector)
* `metricInner_add_left ...`    (algebra lemmas, bare names)

Each wrapper takes `[RiemannianManifold M]` as instance argument and
delegates to the underlying `RiemannianMetric.X` method on
`RiemannianManifold.metric`. Wrappers are `abbrev` / direct delegations
so `g.X`-style proofs still work via abbrev unfolding, and so the
`@[simp]` / `@[metric_simp]` simp sets unify naturally with the
underlying method-form lemmas. -/

section MetricAPI

variable {M : Type*} [TopologicalSpace M] [rm : RiemannianManifold M]

/-- The **metric inner product** $\langle V, W\rangle_g$ as a top-level
function, sourcing $g$ from `[RiemannianManifold M]`. -/
noncomputable abbrev metricInner (x : M)
    (v w : TangentSpace rm.modelI x) : ℝ :=
  rm.metric.metricInner x v w

@[simp]
theorem metricInner_apply (x : M) (v w : TangentSpace rm.modelI x) :
    metricInner x v w = rm.metric.inner x v w := rfl

/-- **Symmetry**: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (x : M) (v w : TangentSpace rm.modelI x) :
    metricInner x v w = metricInner x w v :=
  rm.metric.metricInner_comm x v w

/-- **Positive-definiteness**: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (x : M) (v : TangentSpace rm.modelI x)
    (hv : v ≠ 0) : 0 < metricInner x v v :=
  rm.metric.metricInner_self_pos x v hv

@[metric_simp]
theorem metricInner_add_left (x : M) (v₁ v₂ w : TangentSpace rm.modelI x) :
    metricInner x (v₁ + v₂) w = metricInner x v₁ w + metricInner x v₂ w :=
  rm.metric.metricInner_add_left x v₁ v₂ w

@[metric_simp]
theorem metricInner_add_right (x : M) (v w₁ w₂ : TangentSpace rm.modelI x) :
    metricInner x v (w₁ + w₂) = metricInner x v w₁ + metricInner x v w₂ :=
  rm.metric.metricInner_add_right x v w₁ w₂

@[metric_simp]
theorem metricInner_smul_left (x : M) (c : ℝ)
    (v w : TangentSpace rm.modelI x) :
    metricInner x (c • v) w = c * metricInner x v w :=
  rm.metric.metricInner_smul_left x c v w

@[metric_simp]
theorem metricInner_smul_right (x : M) (c : ℝ)
    (v w : TangentSpace rm.modelI x) :
    metricInner x v (c • w) = c * metricInner x v w :=
  rm.metric.metricInner_smul_right x c v w

@[simp, metric_simp]
theorem metricInner_zero_left (x : M) (w : TangentSpace rm.modelI x) :
    metricInner x 0 w = 0 :=
  rm.metric.metricInner_zero_left x w

@[simp, metric_simp]
theorem metricInner_zero_right (x : M) (v : TangentSpace rm.modelI x) :
    metricInner x v 0 = 0 :=
  rm.metric.metricInner_zero_right x v

@[simp, metric_simp]
theorem metricInner_neg_left (x : M) (v w : TangentSpace rm.modelI x) :
    metricInner x (-v) w = -metricInner x v w :=
  rm.metric.metricInner_neg_left x v w

@[simp, metric_simp]
theorem metricInner_neg_right (x : M) (v w : TangentSpace rm.modelI x) :
    metricInner x v (-w) = -metricInner x v w :=
  rm.metric.metricInner_neg_right x v w

@[simp, metric_simp]
theorem metricInner_sub_left (x : M) (v₁ v₂ w : TangentSpace rm.modelI x) :
    metricInner x (v₁ - v₂) w = metricInner x v₁ w - metricInner x v₂ w :=
  rm.metric.metricInner_sub_left x v₁ v₂ w

@[simp, metric_simp]
theorem metricInner_sub_right (x : M) (v w₁ w₂ : TangentSpace rm.modelI x) :
    metricInner x v (w₁ - w₂) = metricInner x v w₁ - metricInner x v w₂ :=
  rm.metric.metricInner_sub_right x v w₁ w₂

@[simp, metric_simp]
theorem metricInner_self_nonneg (x : M) (v : TangentSpace rm.modelI x) :
    0 ≤ metricInner x v v :=
  rm.metric.metricInner_self_nonneg x v

/-- **Non-degeneracy**: vectors with equal inner-products against every test
vector are equal. -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace rm.modelI x) :
    (∀ z : TangentSpace rm.modelI x, metricInner x v z = metricInner x w z) ↔
      v = w :=
  rm.metric.metricInner_eq_iff_eq x v w

/-- **Inverse Riesz**: $\varphi \mapsto V_\varphi$ such that
$g_x(V_\varphi, W) = \varphi(W)$. -/
noncomputable abbrev metricRiesz (x : M)
    (φ : TangentSpace rm.modelI x →L[ℝ] ℝ) : TangentSpace rm.modelI x :=
  rm.metric.metricRiesz x φ

@[simp]
theorem metricRiesz_inner (x : M)
    (φ : TangentSpace rm.modelI x →L[ℝ] ℝ) (v : TangentSpace rm.modelI x) :
    metricInner x (metricRiesz x φ) v = φ v :=
  rm.metric.metricRiesz_inner x φ v

theorem metricRiesz_unique (x : M) (v : TangentSpace rm.modelI x)
    (φ : TangentSpace rm.modelI x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz x φ :=
  rm.metric.metricRiesz_unique x v φ h

/-- The **metric-to-dual** CLM $V \mapsto g_x(V, \cdot)$. -/
noncomputable abbrev metricToDual (x : M) :
    TangentSpace rm.modelI x →L[ℝ] (TangentSpace rm.modelI x →L[ℝ] ℝ) :=
  rm.metric.metricToDual x

@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace rm.modelI x) :
    metricToDual x v w = metricInner x v w := rfl

theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (M := M) x) :=
  rm.metric.metricToDual_injective x

theorem metricToDual_bijective (x : M) :
    Function.Bijective (metricToDual (M := M) x) :=
  rm.metric.metricToDual_bijective x

/-- The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`. -/
noncomputable abbrev metricToDualEquiv (x : M) :
    TangentSpace rm.modelI x ≃ₗ[ℝ] (TangentSpace rm.modelI x →L[ℝ] ℝ) :=
  rm.metric.metricToDualEquiv x

/-- Smoothness of the metric inner product applied to two smooth tangent
sections. -/
theorem metricInner_mdifferentiableAt [FiniteDimensional ℝ rm.E]
    {Y Z : ∀ y : M, TangentSpace rm.modelI y} {x : M}
    (hY : OpenGALib.TangentSmoothAt Y x) (hZ : OpenGALib.TangentSmoothAt Z x) :
    MDifferentiableAt rm.modelI 𝓘(ℝ, ℝ)
      (fun y => metricInner y (Y y) (Z y)) x :=
  rm.metric.metricInner_mdifferentiableAt hY hZ

end MetricAPI

end OpenGALib
