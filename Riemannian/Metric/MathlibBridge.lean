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
Mathlib provides the **technical foundation**: given a `RiemannianBundle`
instance, Mathlib auto-derives the `NormedAddCommGroup` and
`InnerProductSpace ℝ` instances on each tangent fiber, **derived from
the metric data** (not from a background `[InnerProductSpace ℝ E]`).

This bridge is the link: it converts our `OpenGALib.RiemannianMetric I M`
into a `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` value,
from which Mathlib's typeclass machinery takes over.

## Mathematical correctness

After this bridge fires:
* `inner` on `TangentSpace I x` = `g.metricTensor x` (the geometric metric)
  — NOT background `inner E` (which the previous `instInnerProductSpaceTangent`
  used incorrectly).
* `‖_‖` on `TangentSpace I x` = `√(g.metricTensor x v v)` — the metric-induced norm.
* `stdOrthonormalBasis ℝ (TangentSpace I x)` = a basis g-orthonormal w.r.t.
  `metricInner x` — usable in `LinearMap.trace_eq_sum_inner` for ricci_symm
  proof.

## Phase 1B status

PRE-PAPER spike. Two sub-proofs left as `sorry` in
`OpenGALib.RiemannianMetric.toBundleContMDiffRiemannianMetric`:
* `isVonNBounded` — von Neumann boundedness of `{v | g x v v < 1}` via
  positive-definiteness + finite-dim equivalence of inner products.
* `contMDiff` — bundle-form CLM smoothness from our `g.smoothMetric`.

These are mechanical (provable from existing Mathlib + framework data).
Once filled, the bridge is fully real.

**Ground truth**: Sébastien Gouëzel's pattern in
`Mathlib/Geometry/Manifold/Riemannian/Basic.lean` (line 103,
`riemannianMetricVectorSpace`). -/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace OpenGALib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

/-! ## Phase 1B Spike Conclusion

**Architectural finding** (4 attempts on same `rfl` failure for
`inner ℝ v w = g.toBundleContMDiffRiemannianMetric.inner b v w`):

The `IsContMDiffRiemannianBundle` instance proof requires that `inner ℝ v w`
on `TangentSpace I x` reduces (def-eq) to `g x v w` (the metric tensor).
This requires Mathlib's `Bundle.RiemannianBundle`-derived IPS instance to
fire (priority 80, scoped to `Bundle` namespace).

**Diamond root cause**: while we have `[InnerProductSpace ℝ E]` as a
hypothesis on the model space, Lean's typeclass synthesis finds it via
`TangentSpace I x = E` def-eq (priority 1000) — beating Mathlib's scoped
instance (priority 80). Result: `inner ℝ v w` always resolves to the
background `real_inner_E v w`, NOT the geometric `g x v w`.

**Resolution path** (Phase 1C deep refactor):
* Replace `[InnerProductSpace ℝ E]` with `[NormedSpace ℝ E]` across the
  framework (27+ files). The model space need only be a normed space;
  the IPS structure on each tangent fiber comes from `RiemannianMetric`
  via Mathlib's `RiemannianBundle` machinery.
* Once `[InnerProductSpace ℝ E]` is gone, Mathlib's scoped instance is
  the unique IPS source on `TangentSpace I x` — `rfl` for the
  `IsContMDiffRiemannianBundle` proof obligation will work.

This is the architectural cost of "geometrically correct IPS on tangent
spaces" vs "engineering-convenient background-derived IPS". The spike
has confirmed: **the diamond is structural, not tactical**. No amount
of `set_option backward.isDefEq.respectTransparency` or `letI`
manipulation makes Mathlib's instance win while `[InnerProductSpace ℝ E]`
is in scope.

The `IsContMDiffRiemannianBundle` instance is left out for now;
provided in Phase 1C after the `[NormedSpace ℝ E]` migration. -/

end OpenGALib
