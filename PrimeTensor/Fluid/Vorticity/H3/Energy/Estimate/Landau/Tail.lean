import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Closure

/-!
# Tail-level Landau H³ transport closure

This file packages the pointwise hypotheses needed by the explicit Landau
transport estimate uniformly on a strict H³ tail.  It then feeds that package
into the pre-existing canonical tail growth theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Uniform tail package for the concrete order-by-order Landau transport closure.

At every strict tail time it supplies exactly the flux, pairing, regularity,
integrability, and Landau analytic hypotheses required by
`h3TransportCommutatorBoundAt_of_landauAnalyticData`.
-/
def H3LandauTransportAnalyticOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (h : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo a T →
      H3TransportEnergyFluxVanishesAt u t
        ∧
      H3FirstDerivativeTransportFluxVanishesAt u t
        ∧
      H3OrderOneTransportPairingIntegrableAt u t
        ∧
      H3SecondDerivativeTransportFluxVanishesAt u t
        ∧
      H3OrderTwoTransportPairingIntegrableAt u t
        ∧
      H3OrderThreeTransportRegularityAt u t
        ∧
      H3ThirdDerivativeTransportFluxVanishesAt u t
        ∧
      H3OrderThreeTransportPairingIntegrableAt u t
        ∧
      H3OrderThreeGradientPairingIntegrableAt u t
        ∧
      VelocityH3IntegrableAt u t
        ∧
      H3OrderThreeInterpolationLandauAnalyticDataAt u h t

/--
The uniform Landau analytic tail package supplies the older abstract transport
control package with the concrete universal coefficient `4422`.
-/
theorem h3TransportControlledOnTail_of_landauAnalytic
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hLandau :
        H3LandauTransportAnalyticOnTail
          u a T h
    ) :
    H3TransportControlledOnTail
      u a T h 4422 := by

  intro t ht

  rcases hLandau t ht with
    ⟨
      hFlux0,
      hFlux1,
      hPairing1,
      hFlux2,
      hPairing2,
      hRegular3,
      hFlux3,
      hPairing3,
      hGradientPairing3,
      hH3,
      hAnalytic3
    ⟩

  have hGradient :
      VelocityGradientEnvelope
        u h t :=
    hAnalytic3.2.1

  have hTransport :
      H3TransportCommutatorBoundAt
        u h 4422 t :=
    h3TransportCommutatorBoundAt_of_landauAnalyticData
      hClass
      ht
      hFlux0
      hFlux1
      hPairing1
      hFlux2
      hPairing2
      hRegular3
      hFlux3
      hPairing3
      hGradientPairing3
      hH3
      hAnalytic3

  exact
    ⟨
      hGradient,
      hTransport
    ⟩

/--
Canonical H³ tail growth inequality with the abstract transport-control tail
hypothesis replaced by the explicit Landau analytic tail package.

The normalized canonical H³ energy therefore satisfies the pre-existing growth
profile with the concrete coefficient `4422`.
-/
theorem h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hEnergyAnalytic :
        H3EnergyEstimateAnalyticOnTail
          u a T
    )
    (
      hLandau :
        H3LandauTransportAnalyticOnTail
          u a T h
    ) :
    H3GradientGrowthInequalityFrom
      a T h
      (velocityH3EnergyAt u)
      4422 := by

  have hTransport :
      H3TransportControlledOnTail
        u a T h 4422 :=
    h3TransportControlledOnTail_of_landauAnalytic
      hClass
      hLandau

  exact
    h3GradientGrowthInequalityFrom_canonical
      hClass
      hEnergyAnalytic
      hTransport

end Euclidean
end Bridge
end PrimeTensor
