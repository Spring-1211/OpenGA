import OpenGALib.Riemannian.Connection
import OpenGALib.Riemannian.Metric

/-!
# Riemannian notation — connection tier

Notations for connection-level and metric-level primitives. Imported by
`Connection.lean` (Bianchi section) so the Riemann curvature def can read in
math notation; imported by all downstream theorem code that uses
`∇`, `⟦,⟧`, `⟪,⟫_g`.

  * `⟪V, W⟫_g` — polymorphic inner product (tangent → `ℝ`,
                 section → `M → ℝ`); via `MetricInnerHom` typeclass
  * `‖V‖²_g`   — polymorphic squared norm (tangent → `ℝ`,
                 section → `M → ℝ`); via `MetricNormSq` typeclass
  * `∇[X] Y`   — `covDeriv X Y` as a section `M → TangentSpace I _`
  * `⟦X, Y⟧`   — `VectorField.mlieBracket _ X Y` as a section

All `scoped` to `Riemannian` (or `OpenGALib` for metric inner). Activate
via `open scoped Riemannian OpenGALib`.

Eta-reduced form (no `fun x => ... x` wrapping) so notation aligns with
simp's beta-reduced normal form. `(∇[X] Y) x` elaborates directly to
`covDeriv X Y x` without a residual lambda.

**Ground truth**: do Carmo 1992 §1.2 (inner product), §2 (covariant
derivative).
-/

namespace OpenGALib

/-! ## Polymorphic norm/inner-product typeclasses

`‖·‖²_g` and `⟪·, ·⟫_g` dispatch through these typeclasses so the same
notation works on tangent vectors (yielding `ℝ`) and on sections /
vector fields (yielding `M → ℝ`). -/

/-- Polymorphic squared norm under the Riemannian metric. -/
class MetricNormSq (V : Type*) (R : outParam Type*) where
  /-- The squared norm `‖·‖²_g`. -/
  normSqG : V → R

/-- Polymorphic inner product under the Riemannian metric. -/
class MetricInnerHom (V W : Type*) (R : outParam Type*) where
  /-- The inner product `⟪·, ·⟫_g`. -/
  innerG : V → W → R

section Instances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianMetric I M]

/-- Pointwise tangent-vector squared norm. -/
noncomputable instance instMetricNormSqTangent (x : M) :
    MetricNormSq (TangentSpace I x) ℝ where
  normSqG v := metricInner x v v

/-- Section-level squared norm: vector field $V$ ↦ scalar function
$y \mapsto \langle V(y), V(y)\rangle_g$. -/
noncomputable instance instMetricNormSqSection :
    MetricNormSq ((y : M) → TangentSpace I y) (M → ℝ) where
  normSqG V := fun y => metricInner y (V y) (V y)

/-- Pointwise tangent-vector inner product. -/
noncomputable instance instMetricInnerHomTangent (x : M) :
    MetricInnerHom (TangentSpace I x) (TangentSpace I x) ℝ where
  innerG v w := metricInner x v w

/-- Section-level inner product: pair of vector fields ↦ scalar function
$y \mapsto \langle V(y), W(y)\rangle_g$. -/
noncomputable instance instMetricInnerHomSection :
    MetricInnerHom ((y : M) → TangentSpace I y) ((y : M) → TangentSpace I y) (M → ℝ) where
  innerG V W := fun y => metricInner y (V y) (W y)

end Instances

/-- The metric inner product $\langle V, W \rangle_g$. Pointwise on
tangent vectors → `ℝ`; on two sections → `M → ℝ`. -/
scoped notation:max "⟪" V ", " W "⟫_g" => MetricInnerHom.innerG V W

/-- The squared norm $\|V\|^2_g$. Pointwise on a tangent vector → `ℝ`;
on a section → `M → ℝ`. -/
scoped notation:max "‖" V "‖²_g" => MetricNormSq.normSqG V

end OpenGALib

namespace Riemannian

/-- The covariant derivative $\nabla_X Y$ as a section. Pointwise:
$(∇[X] Y)(x) = (\nabla_X Y)(x) = $ `covDeriv X Y x`. -/
scoped notation:max "∇[" X "] " Y:max => covDeriv X Y

/-- The manifold Lie bracket $[X, Y]$ as a section. Model `I` inferred
from types. Pointwise: $(⟦X, Y⟧)(x) = $ `mlieBracket _ X Y x`. -/
scoped notation:max "⟦" X ", " Y "⟧" => VectorField.mlieBracket _ X Y

end Riemannian
