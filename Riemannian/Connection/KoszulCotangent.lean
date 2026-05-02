import Riemannian.Connection.Koszul
import Riemannian.Metric.RieszSmooth
import Riemannian.TangentBundle.MFDerivSmooth
import Riemannian.TangentBundle.SmoothVectorField

/-!
# Koszul cotangent CLM section

For `v : E` (chart-frame constant tangent direction) and `Y : SmoothVectorField I M`,
this file builds the **half-Koszul cotangent functional** as a smooth bundle CLM
section. Its Riesz extraction gives $\nabla_v Y$ (Levi-Civita along $v$).

**Used by**: `koszulCovDeriv_const_smoothAt` in `Riemannian/Connection/LeviCivita.lean`. -/

open Bundle VectorField OpenGALib
open scoped ContDiff Manifold Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [g : RiemannianMetric I M]

/-! ## Helpers: flat-typed smoothness of `SmoothVectorField` and `metricInner` -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [RiemannianMetric I M] in
set_option backward.isDefEq.respectTransparency false in
/-- A `SmoothVectorField`'s underlying `Y.toFun : Π y : M, T_yM` viewed as
`M → E` (via `T_yM = E` def-eq) is globally `ContMDiff` under
`IsLocallyConstantChartedSpace`. -/
private theorem SmoothVectorField.contMDiff_E (Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, E) ∞ Y.toFun := by
  intro x
  set e := trivializationAt E (TangentSpace I) x with he_def
  -- Bundle-section smoothness gives chart-coord smoothness via Trivialization.contMDiffAt_iff.
  have h_he : (Bundle.TotalSpace.mk x (Y.toFun x) : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) x
  have h_iff := Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun y : M => (Bundle.TotalSpace.mk y (Y.toFun y) : TangentBundle I M))
    (n := ∞) h_he
  have h_chart_coord : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun y : M => (e ⟨y, Y.toFun y⟩).2) x :=
    (h_iff.mp (Y.smooth x)).2
  -- On baseSet, (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  -- Under IsLocallyConstantChartedSpace, e.cLMA R y = id near x, so equals V y.
  apply h_chart_coord.congr_of_eventuallyEq
  have h_baseSet : e.baseSet ∈ 𝓝 x :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_baseSet, h_chart_eq, h_chart_src] with y hy_base hy_eq hy_src
  show Y.toFun y = (e ⟨y, Y.toFun y⟩).2
  -- (e ⟨y, V y⟩).2 = e.continuousLinearMapAt R y (V y).
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy_base]
  -- e.continuousLinearMapAt R y = id near x via continuousLinearMapAtFlat = id (locally).
  show (Y.toFun y : E) = e.continuousLinearMapAt ℝ y (Y.toFun y)
  show (Y.toFun y : E) =
      TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y (Y.toFun y)
  -- continuousLinearMapAtFlat x y = id near x (locally constant chart).
  have h_id : TangentBundle.continuousLinearMapAtFlat (I := I) (M := M) x y
      = ContinuousLinearMap.id ℝ E := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ y
        = ContinuousLinearMap.id ℝ E
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy_src]
    have h_achart_eq : achart H y = achart H x := Subtype.ext hy_eq
    rw [h_achart_eq]
    ext v
    exact (tangentBundleCore I M).coordChange_self (achart H x) y
      (by simpa [tangentBundleCore_baseSet] using hy_src) v
  rw [h_id]
  rfl

/-- **Smoothness of `g.metricTensor` applied to two `ContMDiff` flat-typed
sections**: `y ↦ g.metricTensor y (V y) (W y)` is `ContMDiff` whenever
`V, W : M → E` are. Uses `g.smoothMetric` + double `clm_apply`. -/
private theorem metricTensor_apply_contMDiff
    {V W : M → E} (hV : ContMDiff I 𝓘(ℝ, E) ∞ V) (hW : ContMDiff I 𝓘(ℝ, E) ∞ W) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => g.metricTensor y (V y) (W y)) := by
  intro x
  have h_metric : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun y : M => g.metricTensor y) x :=
    (g.smoothMetric x)
  exact (h_metric.clm_apply (hV x)).clm_apply (hW x)

/-- **Half-Koszul scalar value** $\tfrac12\,K(v_{\text{const}}, Y, w_{\text{const}})(y)$. -/
noncomputable def koszulCotangentScalar
    (v : E) (Y : SmoothVectorField I M) (w : E) (y : M) : ℝ :=
  (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y

/-- **Half-Koszul cotangent CLM** $w \mapsto \tfrac12\,K(v, Y; w)(y)$ as
`E →L[ℝ] ℝ`. Linearity in `w` via `koszul_smul_right` + `koszul_add_right`. -/
noncomputable def koszulCotangentCLM
    (v : E) (Y : SmoothVectorField I M) (y : M) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => koszulCotangentScalar v Y w y
      map_add' := by
        intro w₁ w₂
        unfold koszulCotangentScalar
        have hY_y : OpenGALib.TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w₁ : OpenGALib.TangentSmoothAt (fun _ : M => w₁) y :=
          (SmoothVectorField.const (I := I) (M := M) w₁).smoothAt y
        have h_const_w₂ : OpenGALib.TangentSmoothAt (fun _ : M => w₂) y :=
          (SmoothVectorField.const (I := I) (M := M) w₂).smoothAt y
        have h_YZ₁ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₁) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w₁
        have h_YZ₂ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w₂) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w₂
        have h_Z₁X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₁) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w₁
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_Z₂X : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w₂) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w₂
            ((SmoothVectorField.const (I := I) (M := M) v).smoothAt y)
        have h_add_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁ + w₂) y
              = koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
                + koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y := by
          have h_sum_eq : ((fun _ : M => w₁ + w₂) : ∀ z : M, TangentSpace I z)
              = (fun _ : M => w₁) + (fun _ : M => w₂) := by
            funext z; rfl
          rw [h_sum_eq]
          exact koszul_add_right (fun _ => v) Y.toFun (fun _ => w₁) (fun _ => w₂)
            y h_YZ₁ h_YZ₂ h_Z₁X h_Z₂X h_const_w₁ h_const_w₂
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => w₁ + w₂) y
            = (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₁) y
              + (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w₂) y
        rw [h_add_factored]
        ring
      map_smul' := by
        intro c w
        unfold koszulCotangentScalar
        -- Use koszul_smul_right with f = (const c).
        have hY_y : OpenGALib.TangentSmoothAt Y.toFun y := Y.smoothAt y
        have h_const_w : OpenGALib.TangentSmoothAt (fun _ : M => w) y :=
          (SmoothVectorField.const (I := I) (M := M) w).smoothAt y
        have h_const_v : OpenGALib.TangentSmoothAt (fun _ : M => v) y :=
          (SmoothVectorField.const (I := I) (M := M) v).smoothAt y
        have hf : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => c) y :=
          mdifferentiableAt_const
        have h_YZ : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' (Y.toFun y') ((fun _ : M => w) y')) y :=
          MDifferentiableAt.metricInner_smoothAt hY_y h_const_w
        have h_ZX : MDifferentiableAt I 𝓘(ℝ, ℝ)
            (fun y' : M => metricInner y' ((fun _ : M => w) y') ((fun _ : M => v) y')) y :=
          MDifferentiableAt.metricInner_smoothAt h_const_w h_const_v
        have h_smul_factored :
            koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => c • w) y
              = c * koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y := by
          have h_eq : (fun _ : M => c • w : ∀ z : M, TangentSpace I z)
              = fun y' : M => (fun _ : M => c) y' • (fun _ : M => w) y' := by
            funext z; rfl
          rw [h_eq]
          exact koszul_smul_right (fun _ => v) Y.toFun (fun _ => w)
            (fun _ : M => c) y hf h_YZ h_ZX h_const_w
        show (1/2 : ℝ) * koszulFunctional (fun _ : M => v) Y.toFun
              (fun _ : M => c • w) y
            = (RingHom.id ℝ) c • ((1/2 : ℝ) *
                koszulFunctional (fun _ : M => v) Y.toFun (fun _ : M => w) y)
        rw [h_smul_factored]
        simp
        ring }

@[simp]
lemma koszulCotangentCLM_apply (v : E) (Y : SmoothVectorField I M) (y : M) (w : E) :
    koszulCotangentCLM v Y y w = koszulCotangentScalar v Y w y := rfl

/-- **Smoothness of the koszul cotangent CLM section** as `M → (E →L[ℝ] ℝ)`.

This is the **single remaining PRE-PAPER sub-sorry** for the connection-level
smoothness clause. Closure plan (entirely mechanical, no paper-level math):

**Step A — scalar smoothness** of `koszulCotangentScalar v Y w` in `y` at every
`x`, for fixed `v, w : E` and `Y : SmoothVectorField`. Decomposes into 6
koszul-term smoothness checks via `unfold koszulFunctional`:

1. `directionalDeriv (fun y' => metricInner y' (Y y') w) y v` — chart-frame constant
   direction `v`, smooth scalar via `metricInner_smoothAt` with smooth `Y` and
   `const w`. Smoothness via `mfderiv_const_dir_smoothAt` (real proof in
   `Riemannian/TangentBundle/MFDerivSmooth.lean`).
2. `directionalDeriv (fun y' => metricInner y' w v) y (Y y)` — smoothly-varying
   direction `Y y` (via `set_option respectTransparency` + def-eq `T_yM = E`).
   Scalar smooth via `metricInner_smoothAt` with two const args.
   Smoothness via `mfderiv_smoothDir_smoothAt`.
3. `directionalDeriv (fun y' => metricInner y' v (Y y')) y w` — chart-frame constant
   direction `w`. Symmetric to (1). Via `mfderiv_const_dir_smoothAt`.
4. `metricInner y (mlieBracket I (const v) Y y) w` — smooth via Mathlib's
   `ContMDiffAt.mlieBracket_vectorField` + `metricInner_smoothAt`.
5. `metricInner y (mlieBracket I Y (const w) y) v` — symmetric to (4).
6. `metricInner y (mlieBracket I (const v) (const w) y) (Y y)` — both args
   chart-frame constants ⇒ `mlieBracket I (const v) (const w) y = 0` (since
   mfderivs of constants vanish under `IsLocallyConstantChartedSpace`).
   Hence the inner product is 0, smooth as the constant zero.

**Step B — CLM-valued lift**: componentwise smoothness from Step A lifted via
the framework's `contMDiffOn_clm_of_components` (Layer 2 smoothness lift,
`Riemannian/TangentBundle/Smoothness.lean`). For each basis element `b_i`,
`koszulCotangentCLM v Y y (b_i) = koszulCotangentScalar v Y (b_i) y` (by
`koszulCotangentCLM_apply`). Smoothness of each component scalar gives
CLM-valued smoothness in finite dim.

No `[I.Boundaryless]` required: `mfderiv_const_dir_smoothAt` and
`mfderiv_smoothDir_smoothAt` are stated in the `MDifferentiableWithinAt`
form internally and bridge to the M-side at-form via
`comp_of_preimage_mem_nhdsWithin`. -/
theorem koszulCotangentCLM_smoothAt
    (v : E) (Y : SmoothVectorField I M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => koszulCotangentCLM v Y y) x := by
  -- Single PRE-PAPER bridge sub-sorry; closure plan in docstring above.
  sorry

end Riemannian
