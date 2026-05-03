import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Riemannian.Metric.Basic

/-!
# Mathlib bridge: `OpenGALib.RiemannianMetric` → `Bundle.RiemannianBundle`

This file provides the bridge from our framework's `OpenGALib.RiemannianMetric I M`
typeclass to Mathlib's `Bundle.RiemannianBundle (fun x ↦ TangentSpace I x)` typeclass.

## Architecture

OpenGALib retains its own `RiemannianMetric I M` as the **public-facing**
domain typeclass (Riemannian-geometry-specific naming, narrow scope).
This bridge converts the framework's data into Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` value.

The bridge is provided for **interoperability / future Mathlib catch-up**.
The framework does NOT route its public IPS API through Mathlib's bundle
path — see "Phase 1C architectural lesson" below for the NACG diamond
that prevents this. The framework's own
`OpenGALib.metricInner` (in `Metric/Basic.lean`) is the canonical
geometric inner product API on tangent vectors, NOT `inner ℝ`.

## Phase 1B/1C status

Two PRE-PAPER closures remain in
`OpenGALib.RiemannianMetric.toBundleContMDiffRiemannianMetric`:
* `isVonNBounded` — von Neumann boundedness of `{v | g x v v < 1}`
  via positive-definiteness + finite-dim equivalence of inner products.
* `contMDiff` — bundle-form CLM smoothness from our `g.smoothMetric`.

These are mechanical (provable from existing Mathlib + framework data).
The bridge instance `instBundleRiemannianBundle` typechecks even with
the sorrys (they're inside the field bodies, not at the instance head).

**Ground truth**: Sébastien Gouëzel's pattern in
`Mathlib/Geometry/Manifold/Riemannian/Basic.lean`
(`riemannianMetricVectorSpace`). -/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- Convert `OpenGALib.RiemannianMetric I M` to Mathlib
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`. -/
noncomputable def RiemannianMetric.toBundleContMDiffRiemannianMetric
    (g : RiemannianMetric I M) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) where
  inner x := g.metricTensor x
  symm x v w := g.symm x v w
  pos x v hv := g.posdef x v hv
  isVonNBounded x := by
    -- {v : E | g.metricTensor x v v < 1} is von Neumann bounded.
    -- Mathematical content: positive-definite continuous bilinear form on
    -- finite-dim normed space gives equivalent inner product → level sets are
    -- bounded ellipsoids.
    sorry
  contMDiff := by
    -- Smoothness as bundle CLM-section: derived from g.smoothMetric (our
    -- smooth metric tensor as M → CLM) by lifting to bundle section.
    sorry

set_option backward.isDefEq.respectTransparency false in
/-- Bridge instance: `OpenGALib.RiemannianMetric` provides `Bundle.RiemannianBundle`. -/
noncomputable instance instBundleRiemannianBundle [g : RiemannianMetric I M] :
    Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
  ⟨(g.toBundleContMDiffRiemannianMetric).toRiemannianMetric⟩

/-! ## Phase 1B/1C Architectural Conclusion

**Phase 1B finding** (4 attempts on the same `rfl` failure):
Mathlib's `Bundle.RiemannianBundle`-derived IPS scoped instance
(priority 80) cannot fire while a background `[InnerProductSpace ℝ E]`
hypothesis is in scope — Lean finds the background instance via
`TangentSpace I x = E` def-eq (priority 1000), beating the scoped one.

**Phase 1C migration** (this commit):
* `[InnerProductSpace ℝ E]` → `[NormedSpace ℝ E]` migrated in 18 files
  where the model-space IPS was gratuitous boilerplate (Connection,
  Curvature, Gradient, TangentBundle, Riesz, Metric, FirstVariation,
  Stationary). The `RiemannianMetric` typeclass declaration now requires
  only `[NormedSpace ℝ E]`.
* Framework bridges added on `TangentSpace I x` (`Metric/Basic.lean`
  `NACGBridge` section): `NormedSpace ℝ`, `IsTopologicalAddGroup`,
  `ContinuousConstSMul ℝ`.
* `[InnerProductSpace ℝ E]` retained where structurally necessary:
  `Instances/EuclideanSpace.lean` (uses `innerSL ℝ`),
  `SecondFundamentalForm.lean` + `Variation/SecondVariation.lean` +
  `Stable.lean` + `AlphaStructural.lean` + `SmoothRegularity.lean`
  (use `stdOrthonormalBasis`),
  `Isoperimetric/ReducedBoundary.TangentHyperplane`
  (uses `Submodule.orthogonal`),
  `Metric/Basic.lean InnerProductBridge`
  (provides background-derived IPS bridge).

**Phase 1C architectural lesson — the irreducible NACG diamond**:
Phase 1C audit confirmed that even with `[InnerProductSpace ℝ E]`
removed, Mathlib's bundle IPS scoped instance does NOT fire under our
framework typeclass cascade. Reason: Mathlib's IPS instance produces
its own `Bundle.instNormedAddCommGroupOfRiemannianBundle...` NACG
on each fiber (= metric-norm), which is **incompatible** with our
`OpenGALib.instNormedAddCommGroupTangent` (= chart-background norm).
Two NACGs on the same type cannot coexist (typeclass diamond by design).

The framework chooses chart-background NACG/norm globally (via the
`TangentSpace I x = E` def-eq path). Mathlib's bundle IPS path is
**not** taken; instead, `Metric/Basic.lean InnerProductBridge`
provides background-derived IPS for downstream files needing
`stdOrthonormalBasis`. The geometric inner product is exposed via
`OpenGALib.metricInner` (in `Metric/Basic.lean`), which is the
framework's official API for Riemannian inner products on tangent
vectors — NOT `inner ℝ v w`.

**Mathematical implication**: `stdOrthonormalBasis ℝ (TangentSpace I x)`
returns a basis orthonormal w.r.t. the chart-background inner product.
For `secondFundamentalFormSqNorm` / `meanCurvature` to be the
geometrically correct Frobenius / trace norm, the basis must be
g-orthonormal. This is a **mathematical limitation** of the current
Phase 1C state, **not** a typecheck failure. Future work
(Phase 4 self-build, or Mathlib upstream catch-up) may construct a
g-orthonormal basis primitive (e.g., via Gram-Schmidt over
`metricInner`) to replace `stdOrthonormalBasis`. The basis is
mathematically correct when `g = innerSL ℝ` (the canonical case in
`EuclideanSpace.lean`).

The `IsContMDiffRiemannianBundle` instance is intentionally not
provided (Mathlib's IPS path is not used). The bridge
`instBundleRiemannianBundle` + `toBundleContMDiffRiemannianMetric`
exists for symbolic/future-Mathlib-catch-up purposes; it carries the
2 sorrys above (`isVonNBounded`, `contMDiff`) as documented PRE-PAPER
mechanical closures. -/

end OpenGALib
