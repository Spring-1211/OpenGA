import OpenGALib.Tensor.Alternating.Basis
import OpenGALib.Tensor.Alternating.Bundle
import OpenGALib.Tensor.Alternating.Comp
import OpenGALib.Tensor.Alternating.Congr
import OpenGALib.Tensor.Alternating.Curry
import OpenGALib.Tensor.Alternating.FDeriv
import OpenGALib.Tensor.Alternating.Flip
import OpenGALib.Tensor.Alternating.Wedge
import OpenGALib.Tensor.DifferentialForm.Basic
import OpenGALib.Tensor.DifferentialForm.Congr
import OpenGALib.Tensor.DifferentialForm.Defs
import OpenGALib.Tensor.DifferentialForm.Rough
import OpenGALib.Tensor.Multilinear.Basis
import OpenGALib.Tensor.Multilinear.Bundle
import OpenGALib.Tensor.Multilinear.Comp
import OpenGALib.Tensor.Multilinear.Curry
import OpenGALib.Tensor.Multilinear.Fiber
import OpenGALib.Tensor.Multilinear.Field
import OpenGALib.Tensor.Multilinear.Flip
import OpenGALib.Tensor.Product.Basis
import OpenGALib.Tensor.Product.Bundle
import OpenGALib.Tensor.Product.Defs
import OpenGALib.Tensor.Product.Fiber
import OpenGALib.Tensor.Product.HomEquiv
import OpenGALib.Tensor.Product.Pretrivialization
import OpenGALib.Tensor.Product.Section

/-!
# Tensor — vector-bundle algebra

Tensor algebra over arbitrary `C^n` vector bundles: continuous multilinear
maps, alternating forms, tensor products, differential forms.

This namespace is **independent of `OpenGALib/Riemannian/`**. Riemannian
specialisations (lower indices via metric, inner product on `(r,s)`-sections)
live under `Riemannian/Tensor/` and consume this layer.

## Layering

```
Algebraic/Auxiliary  ← combinatorial / linear-algebra primitives
       ↑
Tensor/Multilinear   ← continuous multilinear-map vector bundle
       ↑
Tensor/Alternating   ← antisymmetric maps + wedge product
       ↑
Tensor/Product       ← tensor-product vector bundle
       ↑
Tensor/DifferentialForm  ← smooth differential n-forms
       ↑
(consumers)
```

## Sub-modules

### `Tensor/Multilinear/` — continuous multilinear-map bundle

* `Bundle` — vector bundle of continuous multilinear maps
  `Bundle.continuousMultilinearMap 𝕜 s F E`. Smooth vector bundle when `E`
  is `C^n`.
* `Comp` — pre-composition smoothness `compContinuousLinearMapL_diag_contDiff`,
  diamond-resolved via `cpolynomial` route.
* `Basis` — finite-dimensionality + explicit basis indexed by `Fin s → Fin d`.
* `Fiber` — fibre-level normed instances + CLE to model fibre.
* `Field` — `C^n` smooth sections of the multilinear bundle.
* `Flip` — argument-flip equivalences.
* `Curry` — currying isometry `Fin (r+r')` ↔ `Fin r`-of-`Fin r'`.

### `Tensor/Alternating/` — alternating-map bundle + wedge product

* `Bundle`, `Comp`, `Congr`, `FDeriv`, `Flip` — bundle structure + composition
  + index reordering + Fréchet derivative + flip.
* `Curry` — uncurryFin / curryFin / uncurrySum (uncurry over shuffles).
* `Basis` — elementary k-covectors via dual basis.
* `Wedge` — wedge product, bilinearity, sign, associativity, graded Leibniz,
  basis expansion.

### `Tensor/Product/` — tensor-product vector bundle

* `HomEquiv` — tensor-hom equivalence + induced normed structure.
* `Defs` — `TensorProduct.mapL` / `mapLBilinear` + alternating tensor product.
* `Pretrivialization`, `Bundle`, `Fiber`, `Section`, `Basis` — pretriv +
  vector-bundle structure + fibre + smooth sections + basis.

### `Tensor/DifferentialForm/` — smooth differential forms

* `Defs` — `DifferentialForm n E F` structure + algebra instances + notation
  `Ω^n⟮E, F⟯`. **On normed space `E`, not yet on manifold.**
* `Congr`, `Rough`, `Basic` — index reordering + computational layer +
  polished API.

## Phase B audit note

As of Phase A close-out, this namespace has **no internal consumer in the
rest of OpenGALib** (GMT / Regularity / Riemannian core). It is preserved
as self-contained tooling, suitable for future:

* Mathlib upstream PR candidates (each sub-module is largely
  Mathlib-conforming).
* Bridge to `Riemannian.Curvature` (planned: Riemann tensor as
  `(1,3)`-tensor section).
* Bridge to `Riemannian.Operators` (planned: chart-Christoffel concrete
  Hessian as `pointwiseBilin` carrier).

These bridges are **substantive refactor work** (Phase C tier 3); the
current commit lands the algebraic infrastructure only.
-/
