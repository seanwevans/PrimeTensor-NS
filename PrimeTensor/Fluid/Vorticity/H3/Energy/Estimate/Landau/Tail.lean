import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Closure

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

At every strict tail time it supplies honest whole-space integration-by-parts
data at orders zero through three, together with the nonredundant Landau
analytic hypotheses required by
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
      H3TransportEnergyIntegrationByPartsAt u t
        ∧
      H3FirstDerivativeTransportIntegrationByPartsAt u t
        ∧
      H3SecondDerivativeTransportIntegrationByPartsAt u t
        ∧
      H3ThirdDerivativeTransportIntegrationByPartsAt u t
        ∧
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt u h t

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
      hSobolevFDeriv6 :
        WholeSpaceC1FDerivL2ToL6
    )
    (
      hQuarticIBP :
        WholeSpaceQuarticDerivativeIntegrationByParts
    )
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hData :
        CanonicalH3EnergyDataOnTail
          u a T
    )
    (
      hLandau :
        H3LandauTransportAnalyticOnTail
          u a T h
    ) :
    H3TransportControlledOnTail
      u a T h 4422 := by

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      hSobolevFDeriv6

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6


  intro t ht

  rcases hLandau t ht with
    ⟨
      hIBP0,
      hIBP1,
      hIBP2,
      hIBP3,
      hAnalyticCore3
    ⟩

  have htIco :
      t ∈ Set.Ico a T :=
    ⟨
      le_of_lt ht.1,
      ht.2
    ⟩

  have hH3 :
      VelocityH3IntegrableAt
        u t :=
    hData.1 t htIco

  have hFlux0 :
      H3TransportEnergyFluxVanishesAt
        u t :=
    h3TransportEnergyFluxVanishesAt_of_integrationByParts
      hIBP0

  have hFlux1 :
      H3FirstDerivativeTransportFluxVanishesAt
        u t :=
    h3FirstDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP1

  have hPurePairing1 :
      H3OrderOnePureTransportPairingIntegrableAt
        u t :=
    h3OrderOnePureTransportPairingIntegrableAt_of_integrationByParts
      hClass
      ht
      hIBP1

  have hFlux2 :
      H3SecondDerivativeTransportFluxVanishesAt
        u t :=
    h3SecondDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP2

  have hPurePairing2 :
      H3OrderTwoPureTransportPairingIntegrableAt
        u t :=
    h3OrderTwoPureTransportPairingIntegrableAt_of_integrationByParts
      hClass
      ht
      hIBP2

  have hFlux3 :
      H3ThirdDerivativeTransportFluxVanishesAt
        u t :=
    h3ThirdDerivativeTransportFluxVanishesAt_of_integrationByParts
      hIBP3

  have hPurePairing3 :
      H3OrderThreePureTransportPairingIntegrableAt
        u t :=
    h3OrderThreePureTransportPairingIntegrableAt_of_integrationByParts
      hClass
      ht
      hIBP3

  have hAnalytic3 :
      H3OrderThreeInterpolationLandauAnalyticDataAt
        u h t :=
    h3OrderThreeInterpolationLandauAnalyticDataAt_of_core
      hSobolev
      hQuarticIBP
      hClass
      ht
      hH3
      hAnalyticCore3

  have hGradient :
      VelocityGradientEnvelope
        u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using
      hAnalyticCore3

  have hPairing1 :
      H3OrderOneTransportPairingIntegrableAt
        u t :=
    h3OrderOneTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3
      hGradient
      hPurePairing1

  have hPairing2 :
      H3OrderTwoTransportPairingIntegrableAt
        u t :=
    h3OrderTwoTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hH3
      hGradient
      hPurePairing2

  have hRegular3 :
      H3OrderThreeTransportRegularityAt
        u t :=
    h3OrderThreeTransportRegularityAt_of_energyClass
      hClass
      ht

  have hGradientPairing3 :
      H3OrderThreeGradientPairingIntegrableAt
        u t :=
    h3OrderThreeGradientPairingIntegrableAt_of_energyClass
      hClass
      ht
      hH3
      hGradient

  have hMonomialPairing3 :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic3

  have hInterpolationPairing3 :
      H3OrderThreeInterpolationPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing3

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt
        u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pure
      hClass
      ht
      hGradientPairing3
      hInterpolationPairing3
      hPurePairing3

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
      hSobolevFDeriv6 :
        WholeSpaceC1FDerivL2ToL6
    )
    (
      hQuarticIBP :
        WholeSpaceQuarticDerivativeIntegrationByParts
    )
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hData :
        CanonicalH3EnergyDataOnTail
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

  have hSobolev6 :
      WholeSpaceC1H1ToL6 :=
    wholeSpaceC1H1ToL6_of_fderiv
      hSobolevFDeriv6

  have hSobolev :
      WholeSpaceC1H1ToL4 :=
    wholeSpaceC1H1ToL4_of_wholeSpaceC1H1ToL6
      hSobolev6


  have hTransport :
      H3TransportControlledOnTail
        u a T h 4422 :=
    h3TransportControlledOnTail_of_landauAnalytic
      hSobolevFDeriv6
      hQuarticIBP
      hClass
      hData
      hLandau

  exact
    h3GradientGrowthInequalityFrom_canonical
      hClass
      hData.2.2
      hTransport

end Euclidean
end Bridge
end PrimeTensor
