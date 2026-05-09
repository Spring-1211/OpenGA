import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import OpenGALib.Riemannian.Metric

/-!
# Standard Riemannian metric on inner product spaces

The flat-metric `RiemannianMetric` instance: a finite-dimensional real
inner product space `E` viewed as a manifold over itself, with the
standard inner product as the (constant) metric tensor.

Specialises to `EuclideanSpace ℝ (Fin n)`, `ℝ`, and any real Hilbert /
finite-dim inner product space.

## Main results

* `instRiemannianMetricSelf` — the flat metric instance.
* `metricInner_eq_real_inner_self` — `metricInner = ⟪·, ·⟫_ℝ` on `E`.

Reference: do Carmo, *Riemannian Geometry*, §1.1 Example 1.4.
-/

namespace OpenGALib

open scoped ContDiff Manifold InnerProductSpace

/-- The flat metric on a finite-dim inner product space `E`: metric tensor
is the standard `innerSL ℝ`, constant in the basepoint. -/
noncomputable instance instRiemannianMetricSelf
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    RiemannianMetric (𝓘(ℝ, E)) E where
  metricTensor _ := innerSL ℝ
  symm _ v w := by
    show ⟪v, w⟫_ℝ = ⟪w, v⟫_ℝ
    exact real_inner_comm w v
  posdef _ v hv := by
    show 0 < ⟪v, v⟫_ℝ
    exact real_inner_self_pos.mpr hv
  smoothMetric := contMDiff_const

/-- $\langle v, w\rangle_g = \langle v, w\rangle_\mathbb{R}$ on the
flat-metric inner product space. -/
theorem metricInner_eq_real_inner_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (x : E) (v w : E) :
    metricInner (I := 𝓘(ℝ, E)) (M := E) x v w = ⟪v, w⟫_ℝ :=
  rfl

end OpenGALib
