import OpenGALib.Riemannian.Operators.Hessian

/-!
# Laplace–Beltrami operator via trace of the Hessian

The Laplace–Beltrami operator on a smooth scalar function `f : M → ℝ` is the
trace of the Hessian: `Δ_g f x = trace_g (Hess f) x`. With a user-supplied
pointwise bilinear-form Hessian `B : pointwiseBilin I M`, this file defines
`laplacianViaTrace B x := traceFun B x` (the trace against the canonical basis
`Module.finBasis ℝ E`) and records its basic algebraic properties.

The chart-coordinate Voss–Weyl identification of `Δ_g f = trace_g (Hess f)` and
the divergence-of-gradient definition are deferred to a future
`Riemannian/Operators/VossWeyl.lean` (depends on chart machinery + integration,
out of scope here).

**Inspired by** `qinz1yang/differential-geometry/Geometry/Laplacian.lean`
(divergence-of-gradient form). The trace-of-Hessian form chosen here is
self-build, framework-aligned, no integration / chart-Christoffel deps.

**Ground truth**: do Carmo 1992 §3.6 (Laplacian = trace of Hessian).
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
  [RiemannianMetric I M]

/-- The **Laplace–Beltrami operator** as the trace of a pointwise Hessian
bilinear form `B`, computed against the canonical basis:
`Δ_g f x = ∑ i, B x (e_i) (e_i)`.

Clients supply `B` from a concrete construction (chart-Christoffel formula,
`hessianVF f` lifted to a pointwise carrier, etc.). -/
noncomputable def laplacianViaTrace
    (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  traceFun B x

@[simp] lemma laplacianViaTrace_def
    (B : pointwiseBilin (M := M) I) (x : M) :
    laplacianViaTrace (I := I) (M := M) B x = traceFun B x := rfl

/-- Linearity in the bilinear form: `Δ_g (B + C) = Δ_g B + Δ_g C`. -/
theorem laplacianViaTrace_add
    (B C : pointwiseBilin (M := M) I) (x : M) :
    laplacianViaTrace (I := I) (M := M) (B + C) x =
      laplacianViaTrace (I := I) (M := M) B x +
        laplacianViaTrace (I := I) (M := M) C x := by
  simp only [laplacianViaTrace, traceFun]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (B x + C x) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) =
    B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) +
      C x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)
  rfl

/-- Homogeneity in the scalar: `Δ_g (c • B) = c · Δ_g B`. -/
theorem laplacianViaTrace_smul
    (c : ℝ) (B : pointwiseBilin (M := M) I) (x : M) :
    laplacianViaTrace (I := I) (M := M) (c • B) x =
      c * laplacianViaTrace (I := I) (M := M) B x := by
  simp only [laplacianViaTrace, traceFun]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (c • B x) ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) =
    c * B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)
  simp [LinearMap.smul_apply]

/-- The trace–Frobenius Cauchy-Schwarz bound, restated for the Laplacian:
`(Δ_g B x)² ≤ (finrank ℝ E) · frobeniusSqFun B x`. This is the inequality used
downstream of the Bochner identity to bound `(Δf)² ≤ n · |Hess f|²`. -/
theorem laplacianViaTrace_sq_le_dim_mul_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (laplacianViaTrace (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSqFun (I := I) (M := M) B x := by
  simpa [laplacianViaTrace] using
    traceFun_sq_le_dim_mul_frobeniusSqFun (I := I) (M := M) B x

end Operators
end Riemannian
