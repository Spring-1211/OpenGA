import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Gradient
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Hessian of a smooth scalar function on a Riemannian manifold

For a smooth scalar `f : M → ℝ`, the **Hessian** is the symmetric `(0,2)`-tensor
which is the second covariant derivative of `f`. Its pointwise definition reads
$$\operatorname{Hess} f(x)(X, Y) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x).$$

Equivalently `Hess f(X, Y) = X(Y(f)) - (∇_X Y)(f)`.

## Form

This file provides two layers:

1. **Vector-field bilinear form** `hessianVF f X Y x : ℝ` — direct framework
   definition via `covDeriv` + `manifoldGradient` + `metricInner`. One-liner;
   reuses the already-grounded Levi-Civita connection.
2. **Pointwise bilinear-form carrier** `pointwiseBilin I M` and the pure
   linear-algebra Frobenius / trace Cauchy-Schwarz inequality
   `(∑_i B(b_i, b_i))² ≤ n · ∑_{i,j} B(b_i, b_j)²` — the inequality used
   downstream of the Bochner identity to bound `(Δf)² ≤ n · |Hess f|²`.

The chart-Christoffel formula and the smoothness of the Hessian as a section
of the `(0,2)`-bundle are deliberately deferred — they belong with the
chart-machinery / RSTensor layer (step 7) and are orthogonal to the two
algebraic results stated here.

**Inspired by** `qinz1yang/differential-geometry/Geometry/Hessian.lean`
(authors: external lib). The pointwise-bilinear-form layer is re-implemented
from the algebraic content; chart machinery dropped to keep this file
self-contained.

**Ground truth**: do Carmo 1992 §6 ex. 12 (Hessian via second covariant derivative).
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

/-! ## Vector-field bilinear-form definition -/

/-- The **Hessian** of a smooth scalar `f : M → ℝ` as a bilinear form on
vector fields, valued in `M → ℝ`:
$$\operatorname{Hess} f(X, Y)(x) = \langle \nabla_X (\nabla^M f), Y \rangle_g(x).$$

Real `noncomputable def` (no `Classical.choose`) — direct composition of
framework primitives `covDeriv`, `manifoldGradient`, `metricInner`. -/
noncomputable def hessianVF
    [IsLocallyConstantChartedSpace H M]
    (f : M → ℝ) (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  metricInner x (covDeriv X (manifoldGradient f) x) (Y x)

/-! ## Pointwise bilinear-form carrier -/

variable (I) in
/-- A pointwise real-valued bilinear form on the tangent bundle of `M`.
Clients constructing a concrete chart-coordinate Hessian (or any other
bilinear `(0,2)`-tensor on `TM`) wrap their data in this carrier. -/
abbrev pointwiseBilin :=
  ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ

/-- A pointwise bilinear form `B` is *pointwise symmetric* if
`B x v w = B x w v` for all `x`, `v`, `w`. -/
def IsPointwiseSymm (B : pointwiseBilin (M := M) I) : Prop :=
  ∀ x : M, ∀ v w : TangentSpace I x, B x v w = B x w v

/-! ## Frobenius and trace functions, in the canonical basis

Because `TangentSpace I x = E` definitionally, the canonical chosen basis
`Module.finBasis ℝ E` is automatically a basis at every point. Computing the
Frobenius norm squared and trace of `B` against this basis gives the scalar
functions `frobeniusSqFun B` and `traceFun B` on `M`. They are *not*
basis-independent in general (would be only with an orthonormal frame in the
metric inner product); the Cauchy-Schwarz inequality below holds for any basis. -/

/-- The Frobenius norm squared of a pointwise bilinear form `B` against the
canonical basis: `∑ i j, (B x (e i) (e j))²`. -/
def frobeniusSqFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))^2

@[simp] lemma frobeniusSqFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    frobeniusSqFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j))^2 := rfl

/-- The trace of `B` against the canonical basis: `∑ i, B x (e i) (e i)`. -/
def traceFun (B : pointwiseBilin (M := M) I) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i)

@[simp] lemma traceFun_def (B : pointwiseBilin (M := M) I) (x : M) :
    traceFun (I := I) (M := M) B x =
      ∑ i : Fin (Module.finrank ℝ E),
        B x ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) i) := rfl

/-- The Frobenius norm squared is non-negative. -/
lemma frobeniusSqFun_nonneg (B : pointwiseBilin (M := M) I) (x : M) :
    0 ≤ frobeniusSqFun (I := I) (M := M) B x :=
  Finset.sum_nonneg
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-! ## Trace–Frobenius Cauchy-Schwarz

Pure linear-algebra: for any bilinear `B` and finite indexing `ι`, the squared
sum of "diagonal" entries `B(v i)(v i)` is controlled by
`|ι| · ∑_{i,j} B(v i)(v j)²`. -/

/-- Trace–Frobenius Cauchy-Schwarz for any indexing type. -/
theorem bilinForm_trace_sq_le_card_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : ι → V) :
    (∑ i : ι, B (v i) (v i))^2 ≤
      (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 := by
  classical
  have h_diag :
      (∑ i : ι, B (v i) (v i))^2 ≤
        (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ) (s := (Finset.univ : Finset ι))
      (f := fun i => B (v i) (v i))
    simpa [Finset.card_univ] using h
  have h_row : ∀ i : ι,
      (B (v i) (v i))^2 ≤ ∑ j : ι, (B (v i) (v j))^2 := by
    intro i
    have h_mem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ (B (v i) (v j))^2 :=
      fun j _ => sq_nonneg _
    exact Finset.single_le_sum (f := fun j => (B (v i) (v j))^2) h_nonneg h_mem
  have h_sum :
      ∑ i : ι, (B (v i) (v i))^2 ≤ ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
    Finset.sum_le_sum (fun i _ => h_row i)
  have h_card_nonneg : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.zero_le _
  calc (∑ i : ι, B (v i) (v i))^2
      ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (B (v i) (v i))^2 := h_diag
    _ ≤ (Fintype.card ι : ℝ) * ∑ i : ι, ∑ j : ι, (B (v i) (v j))^2 :=
        mul_le_mul_of_nonneg_left h_sum h_card_nonneg

/-- Specialisation to the canonical basis `Module.finBasis ℝ V`. -/
theorem bilinForm_trace_sq_le_dim_mul_frobenius_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Module.Finite ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V) :
    (∑ i : Fin (Module.finrank ℝ V), B (b i) (b i))^2 ≤
      (Module.finrank ℝ V : ℝ) *
        ∑ i : Fin (Module.finrank ℝ V),
          ∑ j : Fin (Module.finrank ℝ V), (B (b i) (b j))^2 := by
  have h := bilinForm_trace_sq_le_card_mul_frobenius_sq (V := V)
    (ι := Fin (Module.finrank ℝ V)) B (fun i => b i)
  simpa [Fintype.card_fin] using h

/-- **Pointwise trace–Frobenius Cauchy-Schwarz**:
`(traceFun B x)² ≤ (finrank ℝ E) · frobeniusSqFun B x`. The form usually quoted
in the Bochner / Lichnerowicz literature, valid for any basis (orthonormality
not needed for the inequality itself). -/
theorem traceFun_sq_le_dim_mul_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 ≤
      (Module.finrank ℝ E : ℝ) * frobeniusSqFun (I := I) (M := M) B x := by
  have h := bilinForm_trace_sq_le_dim_mul_frobenius_sq
    (V := TangentSpace I x) (B := B x) (b := Module.finBasis ℝ E)
  simp only [traceFun_def, frobeniusSqFun_def]
  exact h

/-- The trace square divided by the dimension is bounded above by the Frobenius
norm squared: `(traceFun B x)² / n ≤ frobeniusSqFun B x`. -/
theorem traceFun_sq_div_dim_le_frobeniusSqFun
    (B : pointwiseBilin (M := M) I) (x : M) :
    (traceFun (I := I) (M := M) B x)^2 / (Module.finrank ℝ E : ℝ) ≤
      frobeniusSqFun (I := I) (M := M) B x := by
  have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
  have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  have hbound := traceFun_sq_le_dim_mul_frobeniusSqFun (I := I) (M := M) B x
  exact (div_le_iff₀ hpos).mpr (by linarith [hbound])

end Operators
end Riemannian
