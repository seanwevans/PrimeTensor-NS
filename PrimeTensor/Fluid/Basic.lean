import PrimeTensor.Tensor.Laws

/-!
# Multiplicative fluid-system shell

This file connects the lawful tensor differential calculus to a fluid model
without pretending that the nonlinear transport term has already been derived.

What is native now:
* temporal multiplicative response,
* spatial gradient,
* spatial multiplicative Laplacian,
* multiplicative incompressibility,
* pressure inversion,
* normalized unit-viscosity momentum balance.

What remains abstract:
* advection / material transport.

That abstraction is deliberate.  Classical `(u · ∇)u` contains coefficient
action that we have not yet reconstructed intrinsically in the zero-free
multiplicative language.
-/

namespace PrimeTensor

/-- A scalar field evolving along a positive, externally supplied time carrier. -/
abbrev SpaceTimeScalarField
    (T X A : Type) (dim : Depth) :=
  T → ScalarField X A dim

/-- A vector field evolving along a positive, externally supplied time carrier. -/
abbrev SpaceTimeVectorField
    (T X A : Type) (dim : Depth) :=
  T → VectorField X A dim

/--
Abstract temporal multiplicative differential.

Time is deliberately not encoded by a natural-number index here.  A concrete
positive time carrier can be supplied later.
-/
structure TemporalDifferential (T A : Type) where
  d : (T → A) → T → A

/-- Law-only temporal multiplicative calculus. -/
structure IsMulTemporalDifferential
    {T : Type}
    (Dt : TemporalDifferential T MulReal) : Prop where

  d_one :
    ∀ t : T,
      Dt.d (fun _ => (1 : MulReal)) t = 1

  d_mul :
    ∀ (f g : T → MulReal) (t : T),
      Dt.d (fun s => f s * g s) t =
        Dt.d f t * Dt.d g t

  d_inv :
    ∀ (f : T → MulReal) (t : T),
      Dt.d (fun s => (f s)⁻¹) t =
        (Dt.d f t)⁻¹

namespace Tensor

/-- Componentwise product of multiplicative vectors. -/
def vectorMul {dim : Depth}
    (u v : Vector MulReal dim) :
    Vector MulReal dim :=
  ⟨fun i => u.component i * v.component i⟩

/-- Componentwise inversion of a multiplicative vector. -/
def vectorInv {dim : Depth}
    (u : Vector MulReal dim) :
    Vector MulReal dim :=
  ⟨fun i => (u.component i)⁻¹⟩

end Tensor

namespace TemporalDifferential

/-- Temporal derivative of a spacetime vector field, component by component. -/
def vectorDerivative
    {T X : Type} {dim : Depth}
    (Dt : TemporalDifferential T MulReal)
    (u : SpaceTimeVectorField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  fun t x =>
    ⟨fun i =>
      Dt.d
        (fun s => (u s x).component i)
        t⟩

end TemporalDifferential

/--
Abstract nonlinear transport operator.

This is the only genuinely unresolved Navier--Stokes ingredient in this file.
It will eventually be instantiated from the intrinsic scalar action / material
derivative once that structure has been derived.
-/
structure MulTransport
    (T X : Type) (dim : Depth) where
  act :
    SpaceTimeVectorField T X MulReal dim →
    SpaceTimeVectorField T X MulReal dim

namespace MulFluid

/-- Componentwise product of spacetime vector fields. -/
def vectorMul
    {T X : Type} {dim : Depth}
    (u v : SpaceTimeVectorField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  fun t x => Tensor.vectorMul (u t x) (v t x)

/-- Componentwise inversion of a spacetime vector field. -/
def vectorInv
    {T X : Type} {dim : Depth}
    (u : SpaceTimeVectorField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  fun t x => Tensor.vectorInv (u t x)

/-- Spatial multiplicative gradient of a spacetime scalar field. -/
def gradient
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (p : SpaceTimeScalarField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  fun t => D.gradient (p t)

/-- Pressure enters the normalized momentum balance by multiplicative inversion. -/
def pressureForce
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (p : SpaceTimeScalarField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  vectorInv (gradient D p)

/--
Componentwise spatial multiplicative Laplacian.

This is the normalized unit-viscosity dissipative response.  A general positive
viscosity coefficient requires an intrinsic scalar action, which is not assumed
here.
-/
def laplacianVector
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (u : SpaceTimeVectorField T X MulReal dim) :
    SpaceTimeVectorField T X MulReal dim :=
  fun t x =>
    ⟨fun i =>
      D.laplacian
        (fun y => (u t y).component i)
        x⟩

/--
Multiplicative incompressibility.

The pivot `1` is the neutral volume-response condition.
-/
def Incompressible
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (u : SpaceTimeVectorField T X MulReal dim) : Prop :=
  ∀ t x,
    D.divergence (u t) x = 1

/--
Normalized multiplicative momentum balance.

For every spacetime point and every positive spatial axis,

    temporal response * transport response
      =
    inverse pressure-gradient response * Laplacian response.

This is the direct product-form counterpart of an additive balance after
logarithmic conjugation, with the transport operator intentionally abstract.
-/
def MomentumBalance
    {T X : Type} {dim : Depth}
    (Dt : TemporalDifferential T MulReal)
    (D : Differential X MulReal dim)
    (A : MulTransport T X dim)
    (u : SpaceTimeVectorField T X MulReal dim)
    (p : SpaceTimeScalarField T X MulReal dim) : Prop :=
  ∀ t x i,
    (Dt.vectorDerivative u t x).component i *
        (A.act u t x).component i =
      (pressureForce D p t x).component i *
        (laplacianVector D u t x).component i

/--
A multiplicative fluid solution packages the fields and the two governing
constraints, while keeping the transport semantics explicit in `A`.
-/
structure Solution
    {T X : Type} {dim : Depth}
    (Dt : TemporalDifferential T MulReal)
    (D : Differential X MulReal dim)
    (A : MulTransport T X dim) where

  velocity :
    SpaceTimeVectorField T X MulReal dim

  pressure :
    SpaceTimeScalarField T X MulReal dim

  incompressible :
    Incompressible D velocity

  momentum :
    MomentumBalance Dt D A velocity pressure

/--
Multiplicative incompressibility is closed under componentwise multiplication.
-/
theorem incompressible_vectorMul
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (hD : IsMulDifferential D)
    {u v : SpaceTimeVectorField T X MulReal dim}
    (hu : Incompressible D u)
    (hv : Incompressible D v) :
    Incompressible D (vectorMul u v) := by

  intro t x

  change
    D.divergence
        (Differential.vectorMul (u t) (v t))
        x =
      1

  rw [Differential.divergence_vectorMul
    D hD (u t) (v t) x]

  rw [hu t x, hv t x]
  exact MulReal.one_mul 1

/--
Multiplicative incompressibility is closed under componentwise inversion.
-/
theorem incompressible_vectorInv
    {T X : Type} {dim : Depth}
    (D : Differential X MulReal dim)
    (hD : IsMulDifferential D)
    {u : SpaceTimeVectorField T X MulReal dim}
    (hu : Incompressible D u) :
    Incompressible D (vectorInv u) := by

  intro t x

  change
    D.divergence
        (Differential.vectorInv (u t))
        x =
      1

  rw [Differential.divergence_vectorInv
    D hD (u t) x]

  rw [hu t x]
  exact MulReal.inv_one

end MulFluid

end PrimeTensor
