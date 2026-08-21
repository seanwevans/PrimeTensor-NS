import PrimeTensor.Analysis.PowerGrowth
import PrimeTensor.Tensor.Calculus

/-!
# Lawful multiplicative tensor differential calculus

`Differential.d` is intentionally abstract.  This file supplies the algebraic
laws that a concrete multiplicative directional derivative must satisfy.

The interface adds no operations to the scalar carrier.  It only states that
each directional derivative preserves the native multiplicative structure:
the pivot, multiplication, and inversion.

From those three laws we derive ratio, gradient, divergence, and Laplacian
identities.
-/

namespace PrimeTensor

/--
A multiplicative differential obeys the native scalar calculus laws.

This is deliberately a law-only structure, analogous to `IsMulCarrier`.
-/
structure IsMulDifferential
    {X : Type} {dim : Depth}
    (D : Differential X MulReal dim) : Prop where

  d_one :
    ∀ (i : Axis dim) (x : Point X dim),
      D.d i (fun _ => (1 : MulReal)) x = 1

  d_mul :
    ∀ (i : Axis dim)
      (f g : ScalarField X MulReal dim)
      (x : Point X dim),
      D.d i (fun y => f y * g y) x =
        D.d i f x * D.d i g x

  d_inv :
    ∀ (i : Axis dim)
      (f : ScalarField X MulReal dim)
      (x : Point X dim),
      D.d i (fun y => (f y)⁻¹) x =
        (D.d i f x)⁻¹

namespace Axis

/--
A positive-dimensional fold distributes over pointwise multiplication in
`MulReal`.
-/
theorem fold_mul_mulReal :
    ∀ (dim : Depth)
      (f g : Axis dim → MulReal),
      fold (· * ·) dim (fun i => f i * g i) =
        fold (· * ·) dim f *
        fold (· * ·) dim g
  | .one, f, g => rfl
  | .succ dim, f, g => by
      change
        (f .first * g .first) *
            fold (· * ·) dim
              (fun i => f (.next i) * g (.next i)) =
          (f .first *
              fold (· * ·) dim (fun i => f (.next i))) *
            (g .first *
              fold (· * ·) dim (fun i => g (.next i)))
      rw [fold_mul_mulReal dim
        (fun i => f (.next i))
        (fun i => g (.next i))]
      exact MulReal.mul_four_shuffle
        (f .first)
        (g .first)
        (fold (· * ·) dim (fun i => f (.next i)))
        (fold (· * ·) dim (fun i => g (.next i)))

/--
A positive-dimensional fold commutes with pointwise inversion in `MulReal`.
-/
theorem fold_inv_mulReal :
    ∀ (dim : Depth)
      (f : Axis dim → MulReal),
      fold (· * ·) dim (fun i => (f i)⁻¹) =
        (fold (· * ·) dim f)⁻¹
  | .one, f => rfl
  | .succ dim, f => by
      change
        (f .first)⁻¹ *
            fold (· * ·) dim
              (fun i => (f (.next i))⁻¹) =
          (f .first *
            fold (· * ·) dim
              (fun i => f (.next i)))⁻¹
      rw [fold_inv_mulReal dim
        (fun i => f (.next i))]
      symm
      exact MulReal.inv_mul_pair
        (f .first)
        (fold (· * ·) dim
          (fun i => f (.next i)))

end Axis

namespace IsMulDifferential

variable
  {X : Type}
  {dim : Depth}
  {D : Differential X MulReal dim}

/-- Directional product law as an equality of scalar fields. -/
theorem d_mul_field
    (hD : IsMulDifferential D)
    (i : Axis dim)
    (f g : ScalarField X MulReal dim) :
    D.d i (fun y => f y * g y) =
      fun x => D.d i f x * D.d i g x := by
  funext x
  exact hD.d_mul i f g x

/-- Directional inversion law as an equality of scalar fields. -/
theorem d_inv_field
    (hD : IsMulDifferential D)
    (i : Axis dim)
    (f : ScalarField X MulReal dim) :
    D.d i (fun y => (f y)⁻¹) =
      fun x => (D.d i f x)⁻¹ := by
  funext x
  exact hD.d_inv i f x

/-- Directional ratio rule. -/
theorem d_ratio
    (hD : IsMulDifferential D)
    (i : Axis dim)
    (f g : ScalarField X MulReal dim)
    (x : Point X dim) :
    D.d i
        (fun y => MulReal.ratio (f y) (g y))
        x =
      MulReal.ratio
        (D.d i f x)
        (D.d i g x) := by
  unfold MulReal.ratio
  rw [hD.d_mul]
  rw [hD.d_inv]

/-- A gradient component preserves the multiplicative pivot. -/
theorem gradient_one_component
    (hD : IsMulDifferential D)
    (x : Point X dim)
    (i : Axis dim) :
    (D.gradient (fun _ => (1 : MulReal)) x).component i =
      1 := by
  exact hD.d_one i x

/-- Gradient product rule, component by component. -/
theorem gradient_mul_component
    (hD : IsMulDifferential D)
    (f g : ScalarField X MulReal dim)
    (x : Point X dim)
    (i : Axis dim) :
    (D.gradient (fun y => f y * g y) x).component i =
      (D.gradient f x).component i *
      (D.gradient g x).component i := by
  exact hD.d_mul i f g x

/-- Gradient inversion rule, component by component. -/
theorem gradient_inv_component
    (hD : IsMulDifferential D)
    (f : ScalarField X MulReal dim)
    (x : Point X dim)
    (i : Axis dim) :
    (D.gradient (fun y => (f y)⁻¹) x).component i =
      ((D.gradient f x).component i)⁻¹ := by
  exact hD.d_inv i f x

/--
Same-axis second directional derivatives preserve products.
-/
theorem d_second_mul
    (hD : IsMulDifferential D)
    (i : Axis dim)
    (f g : ScalarField X MulReal dim)
    (x : Point X dim) :
    D.d i
        (D.d i (fun y => f y * g y))
        x =
      D.d i (D.d i f) x *
      D.d i (D.d i g) x := by
  rw [hD.d_mul_field i f g]
  exact hD.d_mul i (D.d i f) (D.d i g) x

/--
Same-axis second directional derivatives preserve inversion.
-/
theorem d_second_inv
    (hD : IsMulDifferential D)
    (i : Axis dim)
    (f : ScalarField X MulReal dim)
    (x : Point X dim) :
    D.d i
        (D.d i (fun y => (f y)⁻¹))
        x =
      (D.d i (D.d i f) x)⁻¹ := by
  rw [hD.d_inv_field i f]
  exact hD.d_inv i (D.d i f) x

/--
Multiplicative Laplacian product law.

Because both the directional derivative and the positive-dimensional contraction
are multiplicative, the whole Laplacian preserves products.
-/
theorem laplacian_mul
    (hD : IsMulDifferential D)
    (f g : ScalarField X MulReal dim)
    (x : Point X dim) :
    D.laplacian (fun y => f y * g y) x =
      D.laplacian f x *
      D.laplacian g x := by

  unfold Differential.laplacian

  have hcomponents :
      (fun i =>
        D.d i
          (D.d i (fun y => f y * g y))
          x) =
      (fun i =>
        D.d i (D.d i f) x *
        D.d i (D.d i g) x) := by
    funext i
    exact hD.d_second_mul i f g x

  rw [hcomponents]
  exact Axis.fold_mul_mulReal
    dim
    (fun i => D.d i (D.d i f) x)
    (fun i => D.d i (D.d i g) x)

/-- Multiplicative Laplacian inversion law. -/
theorem laplacian_inv
    (hD : IsMulDifferential D)
    (f : ScalarField X MulReal dim)
    (x : Point X dim) :
    D.laplacian (fun y => (f y)⁻¹) x =
      (D.laplacian f x)⁻¹ := by

  unfold Differential.laplacian

  have hcomponents :
      (fun i =>
        D.d i
          (D.d i (fun y => (f y)⁻¹))
          x) =
      (fun i =>
        (D.d i (D.d i f) x)⁻¹) := by
    funext i
    exact hD.d_second_inv i f x

  rw [hcomponents]
  exact Axis.fold_inv_mulReal
    dim
    (fun i => D.d i (D.d i f) x)

end IsMulDifferential

namespace Differential

/-- Pointwise product of multiplicative vector fields. -/
def vectorMul
    {X : Type} {dim : Depth}
    (u v : VectorField X MulReal dim) :
    VectorField X MulReal dim :=
  fun x =>
    ⟨fun i =>
      (u x).component i *
      (v x).component i⟩

/-- Pointwise inversion of a multiplicative vector field. -/
def vectorInv
    {X : Type} {dim : Depth}
    (u : VectorField X MulReal dim) :
    VectorField X MulReal dim :=
  fun x =>
    ⟨fun i => ((u x).component i)⁻¹⟩

/--
Divergence preserves pointwise vector multiplication for a lawful
multiplicative differential.
-/
theorem divergence_vectorMul
    {X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (hD : IsMulDifferential D)
    (u v : VectorField X MulReal dim)
    (x : Point X dim) :
    D.divergence (vectorMul u v) x =
      D.divergence u x *
      D.divergence v x := by

  unfold divergence vectorMul

  have hcomponents :
      (fun i =>
        D.d i
          (fun y =>
            (u y).component i *
            (v y).component i)
          x) =
      (fun i =>
        D.d i
            (fun y => (u y).component i)
            x *
        D.d i
            (fun y => (v y).component i)
            x) := by
    funext i
    exact hD.d_mul i
      (fun y => (u y).component i)
      (fun y => (v y).component i)
      x

  rw [hcomponents]
  exact Axis.fold_mul_mulReal
    dim
    (fun i =>
      D.d i
        (fun y => (u y).component i)
        x)
    (fun i =>
      D.d i
        (fun y => (v y).component i)
        x)

/--
Divergence commutes with pointwise vector inversion.
-/
theorem divergence_vectorInv
    {X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (hD : IsMulDifferential D)
    (u : VectorField X MulReal dim)
    (x : Point X dim) :
    D.divergence (vectorInv u) x =
      (D.divergence u x)⁻¹ := by

  unfold divergence vectorInv

  have hcomponents :
      (fun i =>
        D.d i
          (fun y => ((u y).component i)⁻¹)
          x) =
      (fun i =>
        (D.d i
          (fun y => (u y).component i)
          x)⁻¹) := by
    funext i
    exact hD.d_inv i
      (fun y => (u y).component i)
      x

  rw [hcomponents]
  exact Axis.fold_inv_mulReal
    dim
    (fun i =>
      D.d i
        (fun y => (u y).component i)
        x)

end Differential

end PrimeTensor
