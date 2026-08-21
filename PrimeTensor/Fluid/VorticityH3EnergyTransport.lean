import PrimeTensor.Fluid.VorticityH3EnergyDiffusion

/-!
# H³ transport commutator frontier

The canonical H³ PDE derivative has the sign convention

    E' = diffusion - transport - pressure.

The diffusion term is now known to be nonpositive under its explicit
whole-space integration-by-parts package, and the pressure term vanishes under
its corresponding package plus differentiated incompressibility.

The remaining nonlinear energy-side estimate is therefore a bound on the
transport contribution.  Classical H³ energy estimates obtain this after the
top-order pure advection term cancels by incompressibility and the remaining
commutators are controlled by the velocity-gradient L∞ envelope.

This file isolates that exact nonlinear obligation without pretending the
commutator estimate has already been proved.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Pointwise-in-time H³ transport commutator bound.

The absolute value is intentional: since the PDE derivative contains
`- velocityH3TransportDerivativeAt`, an absolute bound controls the required
sign automatically.
-/
def H3TransportCommutatorBoundAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (h : ℝ → ℝ)
    (A t : ℝ) : Prop :=
  abs
      (
        velocityH3TransportDerivativeAt
          u t
      )
    ≤
  A
    * (1 + |h t|)
    * velocityH3EnergyAt u t

/--
An absolute transport commutator bound gives the upper bound on the negative
transport contribution that appears in the PDE energy identity.
-/
theorem neg_transport_le_of_commutatorBound
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {A t : ℝ}
    (
      hTransport :
        H3TransportCommutatorBoundAt
          u h A t
    ) :
    -
      velocityH3TransportDerivativeAt
        u t
      ≤
    A
      * (1 + |h t|)
      * velocityH3EnergyAt u t := by

  exact
    le_trans
      (neg_le_abs
        (velocityH3TransportDerivativeAt u t))
      hTransport

/--
The same commutator estimate also controls the transport contribution itself.
-/
theorem transport_le_of_commutatorBound
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {A t : ℝ}
    (
      hTransport :
        H3TransportCommutatorBoundAt
          u h A t
    ) :
    velocityH3TransportDerivativeAt
        u t
      ≤
    A
      * (1 + |h t|)
      * velocityH3EnergyAt u t := by

  exact
    le_trans
      (le_abs_self
        (velocityH3TransportDerivativeAt u t))
      hTransport

/--
Tail-level package coupling the velocity-gradient envelope to the nonlinear
transport estimate.
-/
def H3TransportControlledOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (h : ℝ → ℝ)
    (A : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      VelocityGradientEnvelope
          u h t
        ∧
      H3TransportCommutatorBoundAt
        u h A t

/--
The actual nonlinear commutator obligation.

It asks for one universal nonnegative constant in dimension three such that
every H³ energy-class state, at every strict tail time, satisfies the transport
bound whenever `h` is a velocity-gradient envelope.

Proving this proposition requires the top-order incompressible advection
cancellation together with the lower-order product/commutator estimates.
-/
def GradientEnvelopeControlsH3Transport : Prop :=
  ∃ A : ℝ,
    0 ≤ A
      ∧
    ∀
      (
        u :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three
      )
      (a T : ℝ)
      (h : ℝ → ℝ)
      (t : ℝ),
        PreterminalH3EnergyClass
            u a T
          →
        t ∈ Set.Ioo a T
          →
        VelocityGradientEnvelope
            u h t
          →
        H3TransportCommutatorBoundAt
          u h A t

/--
A proof of the universal commutator obligation supplies a concrete transport
bound at any strict H³ tail time.
-/
theorem h3TransportCommutatorBoundAt_of_gradientEnvelopeControl
    (
      hControl :
        GradientEnvelopeControlsH3Transport
    )
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    ) :
    ∃ A : ℝ,
      0 ≤ A
        ∧
      H3TransportCommutatorBoundAt
        u h A t := by

  rcases hControl with
    ⟨A, hA, hBound⟩

  exact
    ⟨
      A,
      hA,
      hBound
        u a T h t
        hClass
        ht
        hGradient
    ⟩

end Euclidean
end Bridge
end PrimeTensor
