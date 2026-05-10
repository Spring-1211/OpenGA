import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OpenGALib.Algebraic.BilinearForm.Basic
import OpenGALib.Algebraic.BilinearForm.Riesz
import OpenGALib.Riemannian.TangentBundle
import OpenGALib.Util.Attributes

/-!
# Riemannian metric

A **Riemannian metric** on a smooth manifold $M$ is a smooth, symmetric,
positive-definite tensor field $g$ assigning an inner product
$g_x : T_xM \times T_xM \to \mathbb{R}$ to each tangent space.

In OpenGALib, `RiemannianMetric I M` is an `abbrev` for Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` — that is,
the metric is *data* (an inhabitant of a structure), not a typeclass
attribute. Operators take a metric `g : RiemannianMetric I M` as an
explicit argument; multiple metrics on the same manifold coexist as
different inhabitants.

This file provides:

1. The `RiemannianMetric` abbreviation.
2. The metric inner product `g.metricInner` and its bilinear-form algebra.
3. Riesz duality `g.metricRiesz : (T_xM)^* \to T_xM`.
4. Smoothness of `g.metricInner` and of the Riesz section.
5. Bridge instances on `TangentSpace I x` (NACG, IPS, FiniteDim, Complete).

## Main definitions

* `RiemannianMetric I M` — alias for the Mathlib bundled metric.
* `g.metricInner x V W = g_x(V, W)` — the inner product.
* `g.metricRiesz x φ` — the unique vector $V$ with $g_x(V, \cdot) = \varphi$.

Reference: do Carmo, *Riemannian Geometry*, §1.2; Lee, *Smooth Manifolds*, Ch. 13.
Mathlib upstream: `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`.
-/

open Bundle
open scoped ContDiff Manifold Topology

namespace OpenGALib

/-! ## The metric type -/

/-- A **Riemannian metric** on a smooth manifold $M$, modelled on
$(E, H, I)$. Defined as Mathlib's `Bundle.ContMDiffRiemannianMetric`
applied to the tangent bundle: the metric is data, not a typeclass
attribute. -/
abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

namespace RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Inner product -/

/-- The **metric inner product** $\langle V, W\rangle_g = g_x(V, W)$. -/
noncomputable def metricInner (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) : ℝ :=
  g.inner x V W

@[simp]
theorem metricInner_apply (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.inner x V W := rfl

/-- **Symmetry**: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.metricInner x W V :=
  g.symm x V W

/-- **Positive-definiteness**: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    0 < g.metricInner x V V :=
  g.pos x V hV

@[metric_simp]
theorem metricInner_add_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ + V₂) W = g.metricInner x V₁ W + g.metricInner x V₂ W := by
  show g.inner x (V₁ + V₂) W = g.inner x V₁ W + g.inner x V₂ W
  rw [(g.inner x).map_add]; rfl

@[metric_simp]
theorem metricInner_add_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ + W₂) = g.metricInner x V W₁ + g.metricInner x V W₂ :=
  (g.inner x V).map_add W₁ W₂

@[metric_simp]
theorem metricInner_smul_left (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x (c • V) W = c * g.metricInner x V W := by
  show g.inner x (c • V) W = c * g.inner x V W
  rw [(g.inner x).map_smul]; rfl

@[metric_simp]
theorem metricInner_smul_right (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x V (c • W) = c * g.metricInner x V W := by
  show g.inner x V (c • W) = c * g.inner x V W
  rw [(g.inner x V).map_smul]; rfl

@[simp, metric_simp]
theorem metricInner_zero_left (g : RiemannianMetric I M)
    (x : M) (W : TangentSpace I x) :
    g.metricInner x 0 W = 0 := by
  show g.inner x 0 W = 0
  rw [(g.inner x).map_zero]; rfl

@[simp, metric_simp]
theorem metricInner_zero_right (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    g.metricInner x V 0 = 0 :=
  (g.inner x V).map_zero

@[simp, metric_simp]
theorem metricInner_neg_left (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x (-V) W = -g.metricInner x V W := by
  show g.inner x (-V) W = -g.inner x V W
  rw [(g.inner x).map_neg]; rfl

@[simp, metric_simp]
theorem metricInner_neg_right (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V (-W) = -g.metricInner x V W :=
  (g.inner x V).map_neg W

@[simp, metric_simp]
theorem metricInner_sub_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ - V₂) W = g.metricInner x V₁ W - g.metricInner x V₂ W := by
  show g.inner x (V₁ - V₂) W = g.inner x V₁ W - g.inner x V₂ W
  rw [(g.inner x).map_sub]; rfl

@[simp, metric_simp]
theorem metricInner_sub_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ - W₂) = g.metricInner x V W₁ - g.metricInner x V W₂ :=
  (g.inner x V).map_sub W₁ W₂

/-- $\langle V, V\rangle_g \ge 0$ for any $V$. -/
@[simp, metric_simp]
theorem metricInner_self_nonneg (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    0 ≤ g.metricInner x V V := by
  rcases eq_or_ne V 0 with hV | hV
  · rw [hV, g.metricInner_zero_left]
  · exact le_of_lt (g.metricInner_self_pos x V hV)

end RiemannianMetric

end OpenGALib

/-! ## TangentSpace instances (chart-background path)

Background-derived `NormedAddCommGroup`, `NormedSpace`, etc. on each
fibre `TangentSpace I x`, transported via `TangentSpace I x = E`. -/

namespace OpenGALib

section TangentSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

set_option backward.isDefEq.respectTransparency false in
instance instNormedAddCommGroupTangent (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

set_option backward.isDefEq.respectTransparency false in
instance instNormedSpaceTangent (x : M) :
    NormedSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (NormedSpace ℝ E)

set_option backward.isDefEq.respectTransparency false in
instance instIsTopologicalAddGroupTangent (x : M) :
    IsTopologicalAddGroup (TangentSpace I x) :=
  inferInstanceAs (IsTopologicalAddGroup E)

set_option backward.isDefEq.respectTransparency false in
instance instContinuousConstSMulTangent (x : M) :
    ContinuousConstSMul ℝ (TangentSpace I x) :=
  inferInstanceAs (ContinuousConstSMul ℝ E)

set_option backward.isDefEq.respectTransparency false in
instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

set_option backward.isDefEq.respectTransparency false in
instance instCompleteSpaceTangent [CompleteSpace E] (x : M) :
    CompleteSpace (TangentSpace I x) :=
  inferInstanceAs (CompleteSpace E)

end TangentSpaceInstances

section TangentSpaceIPS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance instInnerProductSpaceTangent (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (InnerProductSpace ℝ E)

end TangentSpaceIPS

end OpenGALib

/-! ## Riesz duality

In a finite-dim inner product space $V$, every continuous linear functional
$\varphi : V \to \mathbb{R}$ is uniquely represented as $\langle V_\varphi, \cdot\rangle_g$. -/

namespace OpenGALib
namespace RiemannianMetric

section Riesz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bridge from the metric's continuous bilinear form to the
algebraic-core `BilinearForm.Form ℝ E`. -/
private noncomputable def toBilinForm (g : RiemannianMetric I M) (x : M) :
    BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.inner x v w)
    (fun v₁ v₂ w => by
      simp only [show g.inner x (v₁ + v₂) = g.inner x v₁ + g.inner x v₂
        from (g.inner x).map_add v₁ v₂, ContinuousLinearMap.add_apply])
    (fun c v w => by
      simp only [show g.inner x (c • v) = c • g.inner x v
        from (g.inner x).map_smul c v, ContinuousLinearMap.smul_apply])
    (fun v w₁ w₂ => (g.inner x v).map_add w₁ w₂)
    (fun c v w => (g.inner x v).map_smul c w)

omit [FiniteDimensional ℝ E] in
private theorem toBilinForm_isPosDef (g : RiemannianMetric I M) (x : M) :
    BilinearForm.IsPosDef (g.toBilinForm x) := by
  intro v hv
  show 0 < g.inner x v v
  exact g.pos x v hv

/-- **Forward Riesz** $V \mapsto g_x(V, \cdot)$. -/
noncomputable def metricToDual (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.inner x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.metricToDual x v w = g.metricInner x v w := rfl

omit [FiniteDimensional ℝ E] in
theorem metricToDual_injective (g : RiemannianMetric I M) (x : M) :
    Function.Injective (g.metricToDual x) := by
  intro v₁ v₂ h
  apply BilinearForm.toDual_injective (g.toBilinForm_isPosDef x)
  ext w
  show g.inner x v₁ w = g.inner x v₂ w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h

omit [FiniteDimensional ℝ E] in
/-- **Non-degeneracy**: vectors with equal inner-products against everything are equal. -/
theorem metricInner_eq_iff_eq (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, g.metricInner x v Z = g.metricInner x w Z) ↔ v = w :=
  BilinearForm.inner_eq_iff_eq (g.toBilinForm_isPosDef x) v w

private noncomputable def clmDualEquiv (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap

/-- The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`. -/
noncomputable def metricToDualEquiv (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  (BilinearForm.toDualEquiv (g.toBilinForm_isPosDef x)).trans
    (clmDualEquiv (TangentSpace I x))

theorem metricToDual_bijective (g : RiemannianMetric I M) (x : M) :
    Function.Bijective (g.metricToDual x) := by
  refine ⟨g.metricToDual_injective x, ?_⟩
  intro φ
  refine ⟨(g.metricToDualEquiv x).symm φ, ?_⟩
  ext v
  show g.inner x ((g.metricToDualEquiv x).symm φ) v = φ v
  have := (g.metricToDualEquiv x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f v) this

/-- **Inverse Riesz** $\varphi \mapsto V_\varphi$ such that $g_x(V_\varphi, W) = \varphi(W)$. -/
noncomputable def metricRiesz (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  (g.metricToDualEquiv x).symm φ

/-- **Defining property of Riesz**: $\langle \text{metricRiesz}\,\varphi, W\rangle_g = \varphi(W)$. -/
@[simp]
theorem metricRiesz_inner (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (V : TangentSpace I x) :
    g.metricInner x (g.metricRiesz x φ) V = φ V := by
  show g.inner x ((g.metricToDualEquiv x).symm φ) V = φ V
  have := (g.metricToDualEquiv x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f V) this

/-- **Uniqueness**: if $g_x(V, \cdot) = \varphi$, then $V = \text{metricRiesz}\,\varphi$. -/
theorem metricRiesz_unique (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, g.metricInner x v w = φ w) :
    v = g.metricRiesz x φ := by
  apply g.metricToDual_injective x
  ext w
  rw [g.metricToDual_apply, h w]
  show φ w = g.inner x ((g.metricToDualEquiv x).symm φ) w
  have := (g.metricToDualEquiv x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) this.symm

end Riesz

/-! ## Smoothness

The smoothness of the metric inner product and the Riesz section is
inherited from `g.contMDiff` (Mathlib's bundle-form smoothness on
`b ↦ TotalSpace.mk' b (g.inner b)`). The function-form smoothness
`ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ g.inner` is derived via
trivialization unwrapping.

**Note**: this section is left unfinished pending alignment of the
chart-trivialization smoothness machinery with Mathlib's section-form
representation. Downstream operators that depended on
`MDifferentiableAt.metricInner_smoothAt` and `metricRiesz_section_smoothAt`
will be temporarily blocked. -/

end RiemannianMetric

end OpenGALib
