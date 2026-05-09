import OpenGALib.GeometricMeasureTheory.Varifold
import OpenGALib.GeometricMeasureTheory.SecondVariation
import OpenGALib.GeometricMeasureTheory.Variation.SecondVariation
import OpenGALib.GeometricMeasureTheory.HasNormal
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# AltRegularity.GMT.Stable

Stability and Morse-index concepts for varifolds — GMT-level
classification primitives.

## Phase 1.5 (D): file-relocation

`IsStable` previously lived in `OpenGALib/Regularity/AlphaStructural.lean`. It is
moved here because it is a GMT-level concept (a universal quantification
over test functions of `secondVariation`-non-negativity) rather than a
regularity-theory-specific construct. `OpenGALib/Regularity/AlphaStructural.lean`
re-imports.

## Sibling concepts

  * `IsStable V` — $\delta^2 V \ge 0$ for all test functions
    compactly supported away from $\mathrm{sing}\,V$;
  * `IsUnstable V` — there exists a test function with $\delta^2 V < 0$;
  * `MorseIndex V` — dimension of the negative eigenspace of the
    Jacobi operator (stub for future development).

Each carries the smooth-manifold typeclass cascade
`(I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]`
because `sing I V` requires it.

**Ground truth**: Simon 1983 §49; Schoen-Simon 1981 §1; Wickramasekera
2014 §2 — stability appears as condition (S2) of the class
$\mathcal{S}_\alpha$.
-/

open scoped ContDiff Manifold

namespace GeometricMeasureTheory

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasureTheory.MeasureSpace M]

namespace Varifold

/-- $V$ is **stable** (paper §4 Definition 4.1 (S2)):
$\delta^2 V(\varphi, \varphi) \ge 0$ for every smooth scalar normal
deformation $\varphi$ compactly supported away from $\mathrm{sing}\,V$.

**Phase 1.7 body migration**: body uses `Variation.secondVariationFull`
(full Jacobi form: kinetic $|\nabla\varphi|^2$ + curvature
$|A|^2 + \mathrm{Ric}(\nu,\nu)$ contribution, post Phase 1.6 Bridge).
Requires `[Varifold.HasNormal I V]` for the unit normal field.

Carries the smooth-manifold typeclass cascade
`(I : ModelWithCorners) [ChartedSpace H M] [IsManifold I ∞ M]
[CompleteSpace E] [FiniteDimensional ℝ E] [HasNormal I V]`
because `sing I V` requires it and `secondVariationFull` requires the
HasNormal-Bridge cascade. -/
def IsStable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (V : Varifold M) [Varifold.HasNormal I V] : Prop :=
  ∀ φ : M → ℝ, Function.support φ ⊆ (sing I V)ᶜ →
    0 ≤ Variation.secondVariationFull I V φ

/-- $V$ is **unstable**: there exists a test direction with negative
second variation.

**Phase 1.7 body migration**: body uses `Variation.secondVariationFull`,
matching `IsStable`'s migration. -/
def IsUnstable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    [OpenGALib.RiemannianMetric I M]
    (V : Varifold M) [Varifold.HasNormal I V] : Prop :=
  ∃ φ : M → ℝ,
    Function.support φ ⊆ (sing I V)ᶜ ∧
    Variation.secondVariationFull I V φ < 0

/-- The **Morse index** of $V$: dimension of the negative eigenspace
of the Jacobi operator (stub).

**Ground truth**: Simon 1983 §49 (eigenvalue problem for the Jacobi
operator). Stub returning 0; future development will replace with the
actual eigencount via spectral decomposition.

`abbrev` so `rfl` closes `MorseIndex V = 0` directly. -/
abbrev MorseIndex (_V : Varifold M) : ℕ := 0

end Varifold


end GeometricMeasureTheory
