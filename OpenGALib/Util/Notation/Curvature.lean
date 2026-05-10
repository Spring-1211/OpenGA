import OpenGALib.Riemannian.Curvature
import OpenGALib.Riemannian.Gradient
import OpenGALib.Riemannian.SecondFundamentalForm
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Operators.Hessian
import OpenGALib.Util.Notation.Connection

/-!
# Riemannian notation — post-Curvature tier

Notations for quantities defined in `Curvature.lean`, `Gradient.lean`,
`SecondFundamentalForm.lean`. This file imports those math files and
must therefore NOT be imported back by them — it sits strictly
downstream of the curvature math layer.

  * `Ric(X, Y)`         — `ricci X Y` as a section
  * `Ric_g(v, w) x`     — `ricciTensor x v w` (pointwise)
  * `II(X, Y)`          — `secondFundamentalFormScalar X Y` (codim-1)
  * `scal_g[I]`         — `scalarCurvature (I := I)` ($M \to \mathbb{R}$)
  * `H_g[I]`            — `meanCurvature (I := I)` ($M \to \mathbb{R}$)
  * `grad_g[I] f`        — `manifoldGradient (I := I) f` as a section
  * `Δ_g[I] f`           — `Operators.scalarLaplacian (I := I) f`
  * `hess_g[I] f`        — `Operators.hessianBilin (I := I) f` (`(0,2)`-tensor section)

For $|\nabla f|^2_g$ and $|\nabla^2 f|^2_g$ as functions, use the
polymorphic `‖grad_g[I] f‖²_g` and `‖hess_g[I] f‖²_g`. The Bilin-section
instance of `‖·‖²_g` is the Frobenius squared norm.

The Riemann curvature notation `Riem(X, Y) Z` lives in
`Util/Notation/Riemann.lean` so that
`Curvature.lean` itself can use it.

`I` (the model with corners) appears explicitly in the bracketed
operator notations because `f : M → ℝ` and bare `M` do not expose
`I` to typeclass synthesis (REFACTOR_PLAYBOOK §5). For operators
on tangent fields (`Ric`, `Ric_g`, `II`), `I` is recovered from the
field's `TangentSpace I x` type and the bracket is unnecessary.

All `scoped` to `Riemannian`. Eta-reduced for simp-friendly elaboration.

**Ground truth**: do Carmo 1992 §4 (Ricci), §6.2 (second fundamental
form, mean curvature).
-/

namespace OpenGALib

section BilinInstance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Frobenius squared norm on `(0,2)`-tensor sections. Closes the
polymorphic squared-norm story: `‖B‖²_g x = ∑_{ij} B(x)(eᵢ, eⱼ)²`. -/
noncomputable instance instMetricNormSqBilin :
    MetricNormSq (Riemannian.Operators.Bilin (M := M) I) (M → ℝ) where
  normSqG B := fun x => Riemannian.Operators.frobeniusSq (I := I) (M := M) B x

end BilinInstance

end OpenGALib

namespace Riemannian

/-- The Ricci curvature $\mathrm{Ric}(X, Y)$ as a scalar function on
the manifold: $(Ric(X, Y))(x) = $ `ricci X Y x`. -/
scoped notation:max "Ric(" X ", " Y ")" => ricci X Y

/-- The codim-1 second fundamental form scalar $\mathrm{II}(X, Y) :
M \to \mathbb{R}$. -/
scoped notation:max "II(" X ", " Y ")" => secondFundamentalFormScalar X Y

/-- The scalar curvature $\mathrm{scal}_g : M \to \mathbb{R}$.
`I` is bracketed because bare `M` does not expose the model with corners. -/
scoped notation:max "scal_g[" I "]" => scalarCurvature (I := I)

/-- The mean curvature $H_g : M \to \mathbb{R}$.
`I` is bracketed because bare `M` does not expose the model with corners. -/
scoped notation:max "H_g[" I "]" => meanCurvature (I := I)

/-- The manifold gradient $\mathrm{grad}_g f$ as a section
$x \mapsto \nabla^M f(x)$.
`I` is bracketed because `f : M → ℝ` does not expose the model with corners. -/
scoped notation:max "grad_g[" I "] " f:max => manifoldGradient (I := I) f

/-- The function Laplacian $\Delta_g f : M \to \mathbb{R}$
($= \operatorname{tr}_g(\operatorname{Hess} f)$).
`I` is bracketed because `f : M → ℝ` does not expose the model with corners. -/
scoped notation:max "Δ_g[" I "] " f:max => Operators.scalarLaplacian (I := I) f

/-- The Hessian as a `(0,2)`-tensor section
$\operatorname{Hess} f : x \mapsto (v, w) \mapsto \langle \nabla_v\,\nabla^M f, w\rangle_g$.
`I` is bracketed because `f : M → ℝ` does not expose the model with corners.
For the Frobenius squared norm $|\nabla^2 f|^2_g$, use polymorphic
`‖hess_g[I] f‖²_g` (the Bilin-section instance of `‖·‖²_g`). -/
scoped notation:max "hess_g[" I "] " f:max => Operators.hessianBilin (I := I) f

/-- Pointwise Ricci form $\mathrm{Ric}_x(v, w) = \mathrm{Ric}(X, Y)$ evaluated
on tangent vectors $v, w \in T_xM$. -/
scoped notation:max "Ric_g(" v ", " w ") " x:max => ricciTensor x v w

end Riemannian
