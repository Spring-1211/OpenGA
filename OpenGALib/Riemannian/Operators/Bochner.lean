import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Curvature

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
open scoped ContDiff Manifold Bundle

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
    (1 / 2 : ℝ) * scalarLaplacian (I := I) (M := M) (gradNormSq (I := I) f) x
    = hessianSqNorm (I := I) (M := M) f x
      + metricInner x
          (Riemannian.manifoldGradient (I := I) f x)
          (Riemannian.manifoldGradient (I := I)
            (fun y : M => scalarLaplacian (I := I) (M := M) f y) x)
      + Riemannian.ricciTensor (I := I) (M := M) x
          (Riemannian.manifoldGradient (I := I) f x)
          (Riemannian.manifoldGradient (I := I) f x) := by
  sorry

end Operators
end Riemannian
