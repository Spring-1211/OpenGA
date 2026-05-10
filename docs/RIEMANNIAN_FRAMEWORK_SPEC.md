# Riemannian framework spec

This document specifies the typeclass-level definition of the
"Riemannian manifold" object in OpenGALib. It is the reference for
contributors adding new geometric structures or new operators.

The spec is a mathematical artifact, not engineering documentation:
just as a paper §1.1 fixes the formal meaning of `(M, g)` for the rest
of the paper, this file fixes its formal meaning for the rest of the
framework.

## §1 Definitions

### §1.1 Smooth manifold

```
class SmoothManifold (M : Type*) [TopologicalSpace M] where
  E : Type*           -- model fibre, with NACG + NormedSpace ℝ
  H : Type*           -- chart codomain, with TopologicalSpace
  modelI : ModelWithCorners ℝ E H
  -- + chart machinery + IsManifold modelI ∞ M
```

Mathematical content: a topological space $M$ together with a chart
atlas modeled on $H$, factoring through a model with corners
$\text{modelI} : H \to E$, such that the transition functions are
$C^\infty$.

The fields `E, H, modelI` are framework-internal: a downstream
operator that says "let $M$ be a smooth manifold" requires only
`[SmoothManifold M]`, not the five-typeclass cascade.

### §1.2 Riemannian manifold

```
class RiemannianManifold (M : Type*) [TopologicalSpace M]
    extends SmoothManifold M where
  toRiemannianMetric : RiemannianMetric modelI M
```

Mathematical content: a smooth manifold equipped with a smooth,
symmetric, positive-definite tensor field $g_x : T_xM \times T_xM \to
\mathbb{R}$. Equivalent to the textbook data $(M, g)$.

The metric is exposed as a `[RiemannianMetric modelI M]` instance via
`RiemannianManifold.toRiemannianMetric`. Existing operators written
against `RiemannianMetric I M` keep working under this instance.

## §2 Backward-compatibility bridges

For any `[RiemannianManifold M]`, the following typeclasses synthesize
automatically:

* `NormedAddCommGroup E` via `SmoothManifold.normedAddCommGroup_E`
* `NormedSpace ℝ E` via `SmoothManifold.normedSpace_E`
* `TopologicalSpace H` via `SmoothManifold.topologicalSpace_H`
* `ChartedSpace H M` via `SmoothManifold.chartedSpace_M`
* `IsManifold modelI ∞ M` via `SmoothManifold.isManifold_M`
* `RiemannianMetric modelI M` via `RiemannianManifold.toRiemannianMetric`

Operators in `Riemannian/Connection.lean`, `Riemannian/Gradient.lean`,
`Riemannian/Curvature.lean`, etc. take these as separate typeclass
arguments. They all compose under `[RiemannianManifold M]` without
the user mentioning $E, H, \text{modelI}$ explicitly.

## §3 Notation contract

Notations in `Util/Notation/` activate under `open scoped Riemannian
OpenGALib`. Once `[RiemannianManifold M]` is in scope, the user writes:

| Notation         | Meaning                                  |
|------------------|------------------------------------------|
| `metricInner V W`| $g_x(V, W)$                              |
| `⟪V, W⟫_g`       | polymorphic inner product (point/section) |
| `‖V‖²_g`         | polymorphic squared norm                 |
| `grad_g f`       | manifold gradient $\nabla^M f$           |
| `Δ_g f`          | scalar Laplacian $\operatorname{tr}_g \operatorname{Hess} f$ |
| `hess_g f`       | Hessian as `(0,2)`-tensor section         |
| `Ric(X, Y)`      | Ricci tensor on smooth vector fields     |
| `Ric_g(v, w) x`  | Ricci tensor pointwise                   |

Notation never exposes $\text{modelI}$ or $E$. If a notation requires
explicit annotation, the spec is wrong; fix the typeclass, not the
notation.

## §4 Extension policy

To add a new geometric structure on smooth manifolds:

1. Define `class XManifold (M : Type*) [TopologicalSpace M] extends
   SmoothManifold M where ...`.
2. Bundle the structural data fields. Mark typeclass-valued fields with
   square brackets: `[fieldName : SomeTypeclass ...]` so they expose
   as instances automatically.
3. Provide bridge instances to existing structure-specific typeclasses
   if the new structure is a refinement.
4. Add a §1.x entry below documenting the new class and its bridges.
5. Update `Util/Notation/` if the new structure introduces new
   conventional notation (LaTeX-aligned, no machinery suffixes).

### Currently registered structures

* **`§1.1 SmoothManifold M`** — base smooth structure.
* **`§1.2 RiemannianManifold M`** — extends with metric.

(Future: `LorentzianManifold`, `KählerManifold`, `SymplecticManifold`,
`ContactManifold` — all extend `SmoothManifold M` per §4.)

## §5 Anti-patterns

Things this spec prohibits (lint these out in review):

* **Manifold operator with `[I]`-bracket notation**. `Δ_g[I] f` is
  legacy; new code uses `Δ_g f` under `[RiemannianManifold M]`.
* **Operator parameterizing over `I` explicitly** in user-facing
  signature. `(I := I)` belongs in framework internals; user-facing
  defs take `[RiemannianManifold M]` and read `modelI` if needed.
* **Two named defs for the same math object** (e.g. `manifoldGradientNormSq`
  parallel to `‖grad_g f‖²_g`). One canonical form. Polymorphic
  notation if the form recurs across types.
* **Duplicate typeclass fields**. If `XManifold M` extends
  `SmoothManifold M`, do not re-declare `E, H, modelI` — inherit them.

## §6 Versioning

This spec versions with the framework. Breaking changes to a
registered class or its bridge instances require a release note in
the changelog. Adding new classes per §4 is non-breaking.

**Current version**: 0.1 (initial spec, two registered classes).
