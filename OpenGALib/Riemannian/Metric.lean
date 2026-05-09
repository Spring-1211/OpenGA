import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
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

This file provides the public API of the metric as a single verifiable
object, in five layers:

1. The `RiemannianMetric` typeclass.
2. The metric inner product `metricInner` and its bilinear-form algebra.
3. Riesz duality `metricRiesz : (T_xM)^* \to T_xM`.
4. Smoothness of `metricInner` and of the Riesz section.
5. Bridge instances on `TangentSpace I x` (NACG, IPS, FiniteDim, Complete).

## Main definitions

* `RiemannianMetric I M` — the metric typeclass.
* `metricInner x V W = g_x(V, W)` — the inner product.
* `metricRiesz x φ` — the unique vector $V$ with $g_x(V, \cdot) = \varphi$.

## Main results

* `metricInner_self_pos`, `metricInner_self_nonneg` — positive-definiteness.
* `metricInner_comm` — symmetry.
* `metricRiesz_inner` — the defining property of Riesz duality.
* `metricInner_eq_iff_eq` — non-degeneracy: $g_x(V, \cdot) = g_x(W, \cdot)$ iff $V = W$.
* `MDifferentiableAt.metricInner_smoothAt` — smoothness of $\langle Y, Z\rangle_g$.
* `metricRiesz_section_smoothAt` — smoothness of the Riesz section.

Reference: do Carmo, *Riemannian Geometry*, §1.2; Lee, *Smooth Manifolds*, Ch. 13.
-/

open Bundle
open scoped ContDiff Manifold Topology

namespace OpenGALib

/-! ## Typeclass -/

/-- A **Riemannian metric** on $M$: a smooth, symmetric, positive-definite
bilinear form $g_x : E \times E \to \mathbb{R}$ at each point, identified
with $T_xM \times T_xM \to \mathbb{R}$ via the def-eq `TangentSpace I x = E`. -/
@[ext]
class RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  /-- The metric tensor $g_x : E \to_L^{\mathbb{R}} E \to_L^{\mathbb{R}} \mathbb{R}$. -/
  metricTensor : (x : M) → E →L[ℝ] E →L[ℝ] ℝ
  /-- Symmetry: $g_x(V, W) = g_x(W, V)$. -/
  symm : ∀ (x : M) (v w : E), metricTensor x v w = metricTensor x w v
  /-- Positive-definiteness: $V \ne 0 \Rightarrow g_x(V, V) > 0$. -/
  posdef : ∀ (x : M) (v : E), v ≠ 0 → 0 < metricTensor x v v
  /-- $g$ is a smooth section, i.e., a smooth map $M \to (E \to_L^{\mathbb{R}} E \to_L^{\mathbb{R}} \mathbb{R})$. -/
  smoothMetric : ContMDiff I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ metricTensor

/-! ## Inner product -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

/-- Bridge from the continuous bilinear form `g.metricTensor x` to the
algebraic-core `BilinearForm.Form ℝ E`. Forgets continuity (recovered
automatically in finite dim). Engineering layer; not user-facing. -/
private noncomputable def RiemannianMetric.toBilinForm (x : M) : BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.metricTensor x v w)
    (fun v₁ v₂ w => by
      show g.metricTensor x (v₁ + v₂) w = g.metricTensor x v₁ w + g.metricTensor x v₂ w
      rw [(g.metricTensor x).map_add]; rfl)
    (fun c v w => by
      show g.metricTensor x (c • v) w = c • g.metricTensor x v w
      rw [(g.metricTensor x).map_smul]; rfl)
    (fun v w₁ w₂ => (g.metricTensor x v).map_add w₁ w₂)
    (fun c v w => (g.metricTensor x v).map_smul c w)

/-- The **metric inner product** $\langle V, W\rangle_g = g_x(V, W)$. -/
noncomputable def metricInner (x : M) (V W : TangentSpace I x) : ℝ :=
  BilinearForm.inner (RiemannianMetric.toBilinForm (g := g) x) V W

theorem metricInner_apply (x : M) (V W : TangentSpace I x) :
    metricInner x V W = g.metricTensor x V W := by
  show LinearMap.mk₂ ℝ _ _ _ _ _ V W = g.metricTensor x V W
  rfl

/-- **Symmetry**: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (x : M) (V W : TangentSpace I x) :
    metricInner x V W = metricInner x W V := by
  rw [metricInner_apply, metricInner_apply]; exact g.symm x V W

/-- **Positive-definiteness**: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    0 < metricInner x V V := by
  rw [metricInner_apply]; exact g.posdef x V hV

@[metric_simp]
theorem metricInner_add_left (x : M) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (V₁ + V₂) W = metricInner x V₁ W + metricInner x V₂ W :=
  BilinearForm.inner_add_left _ V₁ V₂ W

@[metric_simp]
theorem metricInner_add_right (x : M) (V W₁ W₂ : TangentSpace I x) :
    metricInner x V (W₁ + W₂) = metricInner x V W₁ + metricInner x V W₂ :=
  BilinearForm.inner_add_right _ V W₁ W₂

@[metric_simp]
theorem metricInner_smul_left (x : M) (c : ℝ) (V W : TangentSpace I x) :
    metricInner x (c • V) W = c * metricInner x V W :=
  BilinearForm.inner_smul_left _ c V W

@[metric_simp]
theorem metricInner_smul_right (x : M) (c : ℝ) (V W : TangentSpace I x) :
    metricInner x V (c • W) = c * metricInner x V W :=
  BilinearForm.inner_smul_right _ c V W

@[simp, metric_simp]
theorem metricInner_zero_left (x : M) (W : TangentSpace I x) :
    metricInner x 0 W = 0 :=
  BilinearForm.inner_zero_left _ W

@[simp, metric_simp]
theorem metricInner_zero_right (x : M) (V : TangentSpace I x) :
    metricInner x V 0 = 0 :=
  BilinearForm.inner_zero_right _ V

@[simp, metric_simp]
theorem metricInner_neg_left (x : M) (V W : TangentSpace I x) :
    metricInner x (-V) W = -metricInner x V W :=
  BilinearForm.inner_neg_left _ V W

@[simp, metric_simp]
theorem metricInner_neg_right (x : M) (V W : TangentSpace I x) :
    metricInner x V (-W) = -metricInner x V W :=
  BilinearForm.inner_neg_right _ V W

@[simp, metric_simp]
theorem metricInner_sub_left (x : M) (V₁ V₂ W : TangentSpace I x) :
    metricInner x (V₁ - V₂) W = metricInner x V₁ W - metricInner x V₂ W :=
  BilinearForm.inner_sub_left _ V₁ V₂ W

@[simp, metric_simp]
theorem metricInner_sub_right (x : M) (V W₁ W₂ : TangentSpace I x) :
    metricInner x V (W₁ - W₂) = metricInner x V W₁ - metricInner x V W₂ :=
  BilinearForm.inner_sub_right _ V W₁ W₂

/-- $\langle V, V\rangle_g \ge 0$ for any $V$. -/
@[simp, metric_simp]
theorem metricInner_self_nonneg (x : M) (V : TangentSpace I x) :
    0 ≤ metricInner x V V := by
  rcases eq_or_ne V 0 with hV | hV
  · rw [hV, metricInner_zero_left]
  · exact le_of_lt (metricInner_self_pos x V hV)

end OpenGALib

/-! ## TangentSpace instances (chart-background path)

Background-derived `NormedAddCommGroup`, `NormedSpace`, `IsTopologicalAddGroup`,
`ContinuousConstSMul`, `InnerProductSpace`, `FiniteDimensional`, `CompleteSpace`
on each fibre `TangentSpace I x`, transported via `TangentSpace I x = E`.

The `backward.isDefEq.respectTransparency false` option makes typeclass
synthesis see through `TangentSpace`'s irreducible attribute, mirroring
Mathlib's pattern in `Topology/VectorBundle/Riemannian.lean`.

**Note**: the IPS instance uses the chart-background inner of $E$, *not*
the geometric `metricInner`. Frames produced via `stdOrthonormalBasis` are
orthonormal w.r.t. the background inner; they coincide with $g$-orthonormal
frames only when $g$ is the canonical inner (`Instances/EuclideanSpace.lean`). -/

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

/-! ## Riesz duality

In a finite-dim inner product space $V$, every continuous linear functional
$\varphi : V \to \mathbb{R}$ is uniquely represented as $\langle V_\varphi, \cdot\rangle_g$.
Here we package this fibrewise. -/

section Riesz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [g : RiemannianMetric I M]

omit [FiniteDimensional ℝ E] in
private theorem RiemannianMetric.toBilinForm_isPosDef (x : M) :
    BilinearForm.IsPosDef (RiemannianMetric.toBilinForm (g := g) x) := by
  intro v hv
  show 0 < g.metricTensor x v v
  exact g.posdef x v hv

/-- **Forward Riesz** $V \mapsto g_x(V, \cdot)$. -/
noncomputable def metricToDual (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.metricTensor x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (x : M) (v w : TangentSpace I x) :
    metricToDual (g := g) x v w = metricInner x v w := by
  rw [metricInner_apply]; rfl

omit [FiniteDimensional ℝ E] in
theorem metricToDual_injective (x : M) :
    Function.Injective (metricToDual (g := g) x) := by
  intro v₁ v₂ h
  apply BilinearForm.toDual_injective (RiemannianMetric.toBilinForm_isPosDef (g := g) x)
  ext w
  show g.metricTensor x v₁ w = g.metricTensor x v₂ w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h

omit [FiniteDimensional ℝ E] in
/-- **Non-degeneracy**: vectors with equal inner-products against everything are equal. -/
theorem metricInner_eq_iff_eq (x : M) (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, metricInner x v Z = metricInner x w Z) ↔ v = w :=
  BilinearForm.inner_eq_iff_eq (RiemannianMetric.toBilinForm_isPosDef (g := g) x) v w

private noncomputable def clmDualEquiv (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap

/-- The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`. -/
noncomputable def metricToDualEquiv (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  (BilinearForm.toDualEquiv
    (RiemannianMetric.toBilinForm_isPosDef (g := g) x)).trans
    (clmDualEquiv (TangentSpace I x))

theorem metricToDual_bijective (x : M) :
    Function.Bijective (metricToDual (g := g) x) := by
  refine ⟨metricToDual_injective x, ?_⟩
  intro φ
  refine ⟨(metricToDualEquiv (g := g) x).symm φ, ?_⟩
  ext v
  show g.metricTensor x ((metricToDualEquiv (g := g) x).symm φ) v = φ v
  have := (metricToDualEquiv (g := g) x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f v) this

/-- **Inverse Riesz** $\varphi \mapsto V_\varphi$ such that $g_x(V_\varphi, W) = \varphi(W)$. -/
noncomputable def metricRiesz (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  (metricToDualEquiv (g := g) x).symm φ

/-- **Defining property of Riesz**: $\langle \text{metricRiesz}\,\varphi, W\rangle_g = \varphi(W)$. -/
@[simp]
theorem metricRiesz_inner (x : M) (φ : TangentSpace I x →L[ℝ] ℝ)
    (V : TangentSpace I x) :
    metricInner x (metricRiesz (g := g) x φ) V = φ V := by
  rw [metricInner_apply]
  show g.metricTensor x ((metricToDualEquiv (g := g) x).symm φ) V = φ V
  have := (metricToDualEquiv (g := g) x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f V) this

/-- **Uniqueness**: if $g_x(V, \cdot) = \varphi$, then $V = \text{metricRiesz}\,\varphi$. -/
theorem metricRiesz_unique (x : M) (v : TangentSpace I x)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, metricInner x v w = φ w) :
    v = metricRiesz (g := g) x φ := by
  apply metricToDual_injective (g := g) x
  ext w
  rw [metricToDual_apply, h w]
  show φ w = g.metricTensor x ((metricToDualEquiv (g := g) x).symm φ) w
  have := (metricToDualEquiv (g := g) x).apply_symm_apply φ
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) this.symm

end Riesz

/-! ## Smoothness -/

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [g : RiemannianMetric I M]

/-- **Smoothness of the metric inner product**: for smooth tangent
sections $Y, Z$ at $x$, the scalar $y \mapsto \langle Y(y), Z(y)\rangle_g$
is $C^\infty$ at $x$. -/
theorem MDifferentiableAt.metricInner_smoothAt
    [IsLocallyConstantChartedSpace H M]
    {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => metricInner y (Y y) (Z y)) x := by
  set e := trivializationAt E (TangentSpace I) x with he_def
  have hY' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Y y⟩).2) x :=
    hY.coordSmoothAt
  have hZ' : MDifferentiableAt I 𝓘(ℝ, E) (fun y => (e ⟨y, Z y⟩).2) x :=
    hZ.coordSmoothAt
  have hg : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  have h_symmL : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => TangentBundle.symmLFlat (I := I) (M := M) x y) x :=
    TangentBundle.symmLFlat_mdifferentiableAt x
  have h_compY : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2)) x :=
    h_symmL.clm_apply hY'
  have h_compZ : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2)) x :=
    h_symmL.clm_apply hZ'
  have h_smooth : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => g.metricTensor y
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2))
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2))) x :=
    (hg.clm_apply h_compY).clm_apply h_compZ
  apply h_smooth.congr_of_eventuallyEq
  have h_baseSet_e : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet_e] with y hy
  set_option backward.isDefEq.respectTransparency false in
  have hY_inv :
      TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2) = (Y y : E) := by
    show e.symmL ℝ y (e ⟨y, Y y⟩).2 = (Y y : E)
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Y y)
    have h_eq : (e ⟨y, Y y⟩).2 = e.continuousLinearMapAt ℝ y (Y y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Y y)).symm
    rw [h_eq]
    exact h_round
  set_option backward.isDefEq.respectTransparency false in
  have hZ_inv :
      TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2) = (Z y : E) := by
    show e.symmL ℝ y (e ⟨y, Z y⟩).2 = (Z y : E)
    have h_round := Bundle.Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (e := e) hy (Z y)
    have h_eq : (e ⟨y, Z y⟩).2 = e.continuousLinearMapAt ℝ y (Z y) := by
      have := Bundle.Trivialization.coe_linearMapAt_of_mem (R := ℝ) e hy
      exact (congrFun this (Z y)).symm
    rw [h_eq]
    exact h_round
  show metricInner y (Y y) (Z y) =
      g.metricTensor y
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Y y⟩).2))
        (TangentBundle.symmLFlat (I := I) (M := M) x y ((e ⟨y, Z y⟩).2))
  rw [hY_inv, hZ_inv]
  rfl

/-! ### Riesz section smoothness

To smooth the Riesz section $y \mapsto \text{metricRiesz}_y(\varphi(y))$,
we identify it with `ContinuousLinearMap.inverse (g.metricTensor y) (φ y)`
and apply Mathlib's smooth-inversion lemma. -/

omit [CompleteSpace E] [IsManifold I ∞ M] in
private theorem metricToDual_isInvertible (x : M) :
    (g.metricTensor x : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)).IsInvertible := by
  set CLE : (TangentSpace I x) ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    (metricToDualEquiv (g := g) x).toContinuousLinearEquiv with hCLE_def
  refine ⟨CLE, ?_⟩
  ext v w
  show CLE v w = g.metricTensor x v w
  show (metricToDualEquiv (g := g) x : (TangentSpace I x) → (TangentSpace I x →L[ℝ] ℝ)) v w
    = g.metricTensor x v w
  rfl

omit [CompleteSpace E] [IsManifold I ∞ M] in
private theorem metricRiesz_eq_inverse (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) :
    metricRiesz (g := g) x φ
      = ContinuousLinearMap.inverse
          (g.metricTensor x : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) φ := by
  apply (metricToDual_injective (g := g) x)
  have h_lhs : metricToDual (g := g) x (metricRiesz (g := g) x φ) = φ := by
    ext v
    rw [metricToDual_apply, metricRiesz_inner]
  rw [h_lhs]
  obtain ⟨CLE, hCLE⟩ := metricToDual_isInvertible (g := g) x
  symm
  show metricToDual (g := g) x ((g.metricTensor x).inverse φ) = φ
  rw [show metricToDual (g := g) x = (g.metricTensor x : TangentSpace I x →L[ℝ] _) from rfl,
      ← hCLE]
  rw [ContinuousLinearMap.inverse_equiv CLE]
  exact (CLE.apply_symm_apply φ)

omit [IsManifold I ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem metricInverse_mdifferentiableAt (x : M) :
    MDifferentiableAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)
      (fun y : M => ContinuousLinearMap.inverse
        (g.metricTensor y : E →L[ℝ] E →L[ℝ] ℝ)) x := by
  have h_metric : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) g.metricTensor x :=
    (g.smoothMetric x).mdifferentiableAt (by decide)
  have h_inv_at : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (g.metricTensor x) :=
    (metricToDual_isInvertible (g := g) x).contDiffAt_map_inverse
  have h_inv_at' : MDifferentiableAt 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E)
      ContinuousLinearMap.inverse (g.metricTensor x) :=
    h_inv_at.contMDiffAt.mdifferentiableAt (by decide)
  exact h_inv_at'.comp x h_metric

set_option backward.isDefEq.respectTransparency false in
/-- **Smoothness of the Riesz section**: for a smooth cotangent section
$\varphi : M \to T^*M$, the section $y \mapsto \text{metricRiesz}_y(\varphi(y))$
is smooth at every $x$. -/
theorem metricRiesz_section_smoothAt
    [IsLocallyConstantChartedSpace H M]
    {φ : M → (E →L[ℝ] ℝ)} {x : M}
    (hφ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) φ x) :
    TangentSmoothAt (fun y : M => metricRiesz (g := g) y (φ y)) x := by
  have h_inverse_at := metricInverse_mdifferentiableAt (g := g) x
  have h_apply_E : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y : M => ContinuousLinearMap.inverse (g.metricTensor y) (φ y)) x :=
    h_inverse_at.clm_apply hφ
  have h_eq : (fun y : M => ContinuousLinearMap.inverse (g.metricTensor y) (φ y))
      = (fun y : M => (metricRiesz (g := g) y (φ y) : E)) := by
    funext y
    exact (metricRiesz_eq_inverse y (φ y)).symm
  rw [h_eq] at h_apply_E
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x with he_def
  have h_clma_smooth : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y) x :=
    (TangentBundle.continuousLinearMapAtFlat_contMDiffAt
      (I := I) (M := M) x).mdifferentiableAt (by decide)
  have h_clma_apply : MDifferentiableAt I 𝓘(ℝ, E)
      (fun y : M => TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
        (metricRiesz (g := g) y (φ y))) x :=
    h_clma_smooth.clm_apply h_apply_E
  apply h_clma_apply.congr_of_eventuallyEq
  have h_baseSet : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  filter_upwards [h_baseSet] with y hy
  show (e ⟨y, metricRiesz (g := g) y (φ y)⟩).2
    = TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
        (metricRiesz (g := g) y (φ y))
  show (e ⟨y, metricRiesz (g := g) y (φ y)⟩).2
    = e.continuousLinearMapAt ℝ y (metricRiesz (g := g) y (φ y))
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy _).symm

end Smoothness

end OpenGALib
