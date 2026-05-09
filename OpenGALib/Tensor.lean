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
import OpenGALib.Tensor.Multilinear.Fiber
import OpenGALib.Tensor.Multilinear.Field
import OpenGALib.Tensor.Multilinear.Flip
import OpenGALib.Tensor.Product.Defs
import OpenGALib.Tensor.Product.HomEquiv

/-!
# Tensor — vector-bundle algebra

Tensor algebra over arbitrary `C^n` vector bundles: continuous multilinear
maps, alternating forms, tensor products, mixed `(r,s)`-tensors, differential
forms.

This namespace is **independent of `OpenGALib/Riemannian/`**. Riemannian
specialisations (lower indices via metric, inner product on `(r,s)`-sections)
live under `Riemannian/Tensor/` and consume this layer.

## Sub-modules

* `Tensor/Multilinear/`  — multilinear-map vector bundle (Bundle, Basis,
                            Fiber, Field, Comp).
-/
