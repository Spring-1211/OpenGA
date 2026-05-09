import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TangentBundle

/-!
# `covDeriv` smoothness

Smoothness of `covDeriv (const v) Y y` in `y` for chart-frame constant
direction `v` and a smooth `Y`. Used by `Riemannian.Curvature` linearity
proofs (`curvatureEndo`, `ricciTensor`).
-/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-- $\nabla_{\,\mathrm{const}\,v}\, Y$ is smooth at every $x$ for any
`SmoothVectorField Y` and any chart-frame constant direction $v$. -/
theorem covDeriv_const_smoothVF_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    OpenGALib.TangentSmoothAt
      (fun y : M => covDeriv (fun _ : M => v) Y.toFun y) x :=
  Riemannian.leviCivitaConnection_smoothAt_const_dir Y v x

end Riemannian
