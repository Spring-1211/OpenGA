import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature
import OpenGALib.Util.Notation

/-!
# Bochner–Weitzenböck identity

For a smooth scalar $f : M \to \mathbb{R}$ on a Riemannian manifold $(M, g)$:
$$\tfrac{1}{2}\,\Delta_g \, |\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f,\, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f,\, \nabla f).$$

Reference: Petersen, *Riemannian Geometry*, Ch. 7 §1 Proposition 33;
do Carmo §6 (curvature commutators); Schoen-Simon 1981 §1 (variational
application).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle OpenGALib
open scoped ContDiff Manifold Bundle Riemannian

namespace Riemannian
namespace Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [RiemannianMetric I M]

/-- Squared gradient norm $|\nabla f|_g^2$ as a scalar function. -/
noncomputable def gradNormSq (f : M → ℝ) (y : M) : ℝ :=
  metricInner y (Riemannian.manifoldGradient (I := I) f y)
    (Riemannian.manifoldGradient (I := I) f y)

/-- **Bochner–Weitzenböck identity**:
$$\tfrac{1}{2}\,\Delta_g\,|\nabla f|_g^2
  = |\nabla^2 f|_g^2
    + \langle \nabla f, \nabla\,\Delta_g f\rangle_g
    + \mathrm{Ric}(\nabla f, \nabla f).$$ -/
theorem bochner_weitzenboeck (f : M → ℝ) (x : M) :
    (1 / 2 : ℝ) * (Δ_g[I] (gradNormSq (I := I) f)) x
    = (hessNormSq_g[I] f) x
      + ⟪(grad_g[I] f) x,
         Riemannian.manifoldGradient (I := I) (Δ_g[I] f) x⟫_g
      + Ric_g((grad_g[I] f) x,
              (grad_g[I] f) x) x := by
  sorry

end Operators
end Riemannian
