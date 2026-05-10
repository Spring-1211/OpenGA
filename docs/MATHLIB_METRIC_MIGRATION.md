# Migration plan: `Bundle.ContMDiffRiemannianMetric` alignment

Architectural reset. Replaces the framework-self-built
`class RiemannianMetric I M` (Phase 4.7 design) with a thin alias to
Mathlib's `Bundle.ContMDiffRiemannianMetric`, in line with how
`qinz1yang/differential-geometry` is structured.

## §1 Why

* **Mathematical clarity** (user requirement, 2026-05-10): the
  Riemannian metric is *data on top of the manifold structure*, not a
  typeclass attribute. Mathlib's `Bundle.ContMDiffRiemannianMetric` is
  exactly that: a structure type whose inhabitants are metrics; multiple
  metrics on the same manifold coexist as different values.
* **Mathlib alignment**: stop diverging from upstream. Future
  contributors read Mathlib documentation and apply directly. AI
  agents trained on Mathlib code work without translating our dialect.
* **Drop the `[I]` workaround**: Mathlib's pattern passes `g` as
  explicit value; pointwise notation (`g.inner x V W`) carries `I`
  through `g`'s type. Function-of-`M` operators take `g` explicit too.
  No typeclass-synthesis-with-metavariable problem.
* **`qinz1yang/differential-geometry` precedent**: 275k LOC repo built
  on this pattern (`abbrev SmoothRiemannianMetric I M := Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`,
  `g.inner x V W` everywhere). Validates the path at scale.

## §2 Validation result (2026-05-10)

Smoke test (`Riemannian/MathlibMetricTest.lean`, since deleted): under our
working assumptions
```
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
{H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
```
the type
```
Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)
```
elaborates, `g.inner x V W : ℝ` typechecks, `g.symm`, `g.pos` work.
**No `lean4#13063` diamond bite, no `attribute [-instance]` workaround
needed**. The Phase 4.7 sidestep was not necessary; the path is open.

## §3 Field-name mapping

| Self-built (`class RiemannianMetric I M`) | Mathlib's `ContMDiffRiemannianMetric` |
|---|---|
| `g.metricTensor x v w`     | `g.inner x v w`        |
| `g.symm x v w`             | `g.symm x v w` (same)  |
| `g.posdef x v hv`          | `g.pos x v hv`         |
| `g.smoothMetric`           | `g.contMDiff`          |
| (no equivalent)            | `g.isVonNBounded`      |

## §4 New typeclass surface

```lean
-- Riemannian/SmoothManifold.lean (NEW; extracted from Manifold.lean)
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  E, H, modelI fields  -- as currently in Manifold.lean

-- Riemannian/Metric.lean (REWRITTEN)
abbrev RiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

namespace RiemannianMetric

-- All operators here as methods of `g : RiemannianMetric I M`:
def metricInner (g : RiemannianMetric I M) (x : M) (V W : TangentSpace I x) : ℝ
def metricToDual (g : RiemannianMetric I M) (x : M) : TangentSpace I x →L[ℝ] _
def metricRiesz (g : RiemannianMetric I M) (x : M) : (TangentSpace I x →L[ℝ] ℝ) → TangentSpace I x
-- + all bilinearity, comm, pos, etc. theorems renamed accordingly.

end RiemannianMetric

-- Riemannian/Manifold.lean (UPDATED)
class RiemannianManifold (M : Type*) [TopologicalSpace M] extends SmoothManifold M where
  metric : RiemannianMetric modelI M  -- value, not instance
```

## §5 File migration list

Files using `[g : RiemannianMetric I M]` (instance arg, broken by
class→abbrev) and the migration shape:

| File | Current | New |
|---|---|---|
| `Riemannian/Metric.lean` | class + theorems use `[g : RM I M]` | abbrev + theorems take `(g : RM I M)` |
| `Riemannian/Manifold.lean` | `[toRiemannianMetric : ...]` instance field | `(metric : ...)` regular field |
| `Riemannian/Connection.lean` | `[RM I M]` in variable | `(g : RM I M)` in variable, all `covDeriv X Y` → `covDeriv g X Y` |
| `Riemannian/Curvature.lean` | same | same |
| `Riemannian/Gradient.lean` | same | same |
| `Riemannian/SecondFundamentalForm.lean` | same | same |
| `Riemannian/Operators/Hessian.lean` | same | same |
| `Riemannian/Operators/Laplacian.lean` | same | same |
| `Riemannian/Operators/Bochner.lean` | same | same |
| `Riemannian/Metric/MathlibBridge.lean` | own bridge to Mathlib | drop (Mathlib is now upstream) |
| `Riemannian/Instances/EuclideanSpace.lean` | provides `instance : RM I M` | provides `instance : Bundle.ContMDiffRiemannianMetric ...` (or `def : RM I M`) |
| `GeometricMeasureTheory/Variation/SecondVariation.lean` | uses `[RM I M]` | takes `(g : RM I M)` |
| `GeometricMeasureTheory/Variation/FirstVariation.lean` | same | same |
| `GeometricMeasureTheory/Stationary.lean` | same | same |
| `GeometricMeasureTheory/Stable.lean` | same | same |
| `GeometricMeasureTheory/Isoperimetric/ReducedBoundary.lean` | same | same |
| `Util/Notation/Connection.lean`, `Util/Notation/Curvature.lean` | typeclass-driven notation | rework to fish `g` from `[RiemannianManifold M]` instance |

Total: **16 framework files + 5 GMT files = 21 files**.

## §6 Notation strategy

Two notation tiers:

* **Pointwise notation** (V, W are tangent vectors, type exposes `I`):
  `⟪V, W⟫_g`, `‖V‖²_g`. These dispatch through the `MetricInnerHom` /
  `MetricNormSq` polymorphic typeclasses (already in place from this
  session). Under `[RiemannianManifold M]`, the canonical `g` is read
  from `(RiemannianManifold.metric : RiemannianMetric _ _)`.
* **Function-of-M notation** (`Δ_g f`, `grad_g f`, `hess_g f`):
  desugar to operator calls with the canonical `g` from
  `RiemannianManifold.metric`. Bracket-free by construction (no
  metavariable issue because `g` is read from typeclass field, not
  inferred from `f : M → ℝ`).

For non-canonical metric usage (compare two metrics, conformal
deformation, etc.): users call operators with `g` explicit, e.g.
`g.metricInner x V W` or `manifoldGradient g f x`.

## §7 Execution plan (multi-session)

**Session A** (atomic chunk: foundation + smallest cascade):
1. Extract `SmoothManifold` → `Riemannian/SmoothManifold.lean`.
2. Rewrite `Riemannian/Metric.lean` (class → abbrev, theorems take `(g : ...)` explicit, full namespace).
3. Update `Riemannian/Manifold.lean`.
4. Update `Riemannian/Instances/EuclideanSpace.lean`.
5. Build Metric + Manifold + EuclideanSpace green; commit.

**Session B** (Connection cascade):
1. Update `Riemannian/Connection.lean` (largest dependent).
2. Build green; commit.

**Session C** (Curvature + operators cascade):
1. Update `Riemannian/Curvature.lean`, `Gradient.lean`, `SecondFundamentalForm.lean`.
2. Update `Riemannian/Operators/{Hessian,Laplacian,Bochner}.lean`.
3. Build green; commit.

**Session D** (GMT + notation):
1. Update GMT files (5).
2. Rework `Util/Notation/{Connection,Curvature}.lean`.
3. Build green; commit.

**Session E** (cleanup):
1. Drop `Riemannian/Metric/MathlibBridge.lean` (no longer needed).
2. Update CLAUDE.md to remove Phase 4.7 framing.
3. Update `docs/RIEMANNIAN_FRAMEWORK_SPEC.md` to reflect new types.
4. Drop now-stale REFACTOR_PLAYBOOK §5 (typeclass synthesis with `_`).

Per-session: complete the migration of all listed files; do not commit
mid-cascade. CLAUDE.md governs.

## §8 Risks

* **`isVonNBounded` field**: Mathlib's `ContMDiffRiemannianMetric`
  requires `isVonNBounded`, which our self-built class did not. When
  constructing concrete instances (`Instances/EuclideanSpace.lean`),
  this field needs a proof. Likely automatic for finite-dim
  `[NormedAddCommGroup E]`-derived metrics; verify in Session A.
* **MathlibBridge.lean** sorry: the file currently has 1 sorry that
  may be obviated entirely by the migration (Mathlib's metric IS the
  framework's metric). Verify in Session E.
* **Notation polymorphism**: the `MetricNormSq` / `MetricInnerHom`
  typeclasses introduced this session may need re-instancing once the
  underlying `RiemannianMetric` type changes. Re-instance in Session D.

## §9 Success criteria

* All 21 files green under `lake build`.
* `Bochner` statement reads bracket-free: `(1/2) * Δ_g ‖∇f‖²_g x = ‖∇²f‖²_g x + ⟪∇f, ∇(Δ_g f)⟫_g x + Ric(∇f, ∇f) x`.
* `class RiemannianMetric` no longer exists; `RiemannianMetric I M`
  resolves to Mathlib's structure type.
* `qinz1yang/differential-geometry` reading equivalent: any pure-math
  formalizer comfortable with their idiom can read OpenGALib without
  translation.
