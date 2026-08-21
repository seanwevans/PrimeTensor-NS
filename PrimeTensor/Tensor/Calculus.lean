import PrimeTensor.Tensor.Contract

/-!
# Abstract multiplicative differential calculus

This file deliberately separates differential identities from the eventual
analytic construction of the derivative on completed prime-barcode numbers.
-/

namespace PrimeTensor

/-- A point in a positive-dimensional coordinate space. -/
abbrev Point (X : Type) (dim : Depth) := Axis dim → X

/-- Scalar field. -/
abbrev ScalarField (X A : Type) (dim : Depth) := Point X dim → A

/-- Vector field. -/
abbrev VectorField (X A : Type) (dim : Depth) := Point X dim → Tensor.Vector A dim

/--
An abstract directional derivative. Its concrete multiplicative limit will be
provided only after the completed number carrier is in place.
-/
structure Differential (X A : Type) (dim : Depth) where
  d : Axis dim → ScalarField X A dim → ScalarField X A dim

namespace Differential

/-- Multiplicative gradient. -/
def gradient {X A : Type} {dim : Depth}
    (D : Differential X A dim) (f : ScalarField X A dim) : VectorField X A dim :=
  fun x => ⟨fun i => D.d i f x⟩

/-- Multiplicative divergence: product of diagonal directional derivatives. -/
def divergence {X A : Type} [Mul A] {dim : Depth}
    (D : Differential X A dim) (u : VectorField X A dim) : ScalarField X A dim :=
  fun x =>
    Axis.fold (· * ·) dim (fun i =>
      D.d i (fun y => (u y).component i) x)

/-- Multiplicative Laplacian: product of same-axis second derivatives. -/
def laplacian {X A : Type} [Mul A] {dim : Depth}
    (D : Differential X A dim) (f : ScalarField X A dim) : ScalarField X A dim :=
  fun x =>
    Axis.fold (· * ·) dim (fun i =>
      D.d i (D.d i f) x)

end Differential

end PrimeTensor
