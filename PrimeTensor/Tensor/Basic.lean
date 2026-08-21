import PrimeTensor.Ratio

/-!
# Positive-rank multiplicative tensors

Dimensions and ranks are `Depth`, so neither can be zeroth. Components live in
an arbitrary multiplicative carrier.
-/

namespace PrimeTensor

structure Tensor (A : Type) (dim rank : Depth) where
  component : IndexTuple dim rank → A

namespace Tensor

abbrev Vector (A : Type) (dim : Depth) := Tensor A dim .one
abbrev Matrix (A : Type) (dim : Depth) := Tensor A dim Depth.two

/-- Rank-one component access. -/
def vectorAt {A : Type} {dim : Depth} (v : Vector A dim) (i : Axis dim) : A :=
  v.component i

/-- Rank-two component access. -/
def matrixAt {A : Type} {dim : Depth} (m : Matrix A dim)
    (i j : Axis dim) : A :=
  m.component (i, j)

/-- Pointwise map of tensor coefficients. -/
def map {A B : Type} {dim rank : Depth} (f : A → B)
    (t : Tensor A dim rank) : Tensor B dim rank :=
  ⟨fun i => f (t.component i)⟩

/-- Multiplicative outer product of two vectors. -/
def outer {A : Type} [Mul A] {dim : Depth}
    (u v : Vector A dim) : Matrix A dim :=
  ⟨fun ij => u.component ij.1 * v.component ij.2⟩

end Tensor

end PrimeTensor
