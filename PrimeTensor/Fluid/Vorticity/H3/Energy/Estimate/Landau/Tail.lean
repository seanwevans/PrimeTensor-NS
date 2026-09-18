import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Regularity.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Gradient.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Pairing.Integrability.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Pairing.Integrability.FromPDE
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.IntegrationByParts.OrderOneTwo
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

The order-zero, order-one, and order-two whole-space transport IBP packages
are theorem-level consequences of canonical H³ data plus the gradient envelope.
At order three, canonical PDE pairing integrability plus the independently
integrable commutator recovers the pure-transport pairing integrability.

The only remaining whole-space transport boundary datum is therefore the
vanishing of the top-order scalar flux integral, together with the velocity-
gradient envelope used throughout the commutator estimate.
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
      H3ThirdDerivativeTransportFluxVanishesAt u t
        ∧
      VelocityGradientEnvelope u h t

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
      hFlux3,
      hGradient
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

  have hIBP0 :
      H3TransportEnergyIntegrationByPartsAt
        u t :=
    h3TransportEnergyIntegrationByPartsAt_of_energyClass
      hClass
      ht
      hH3
      hGradient

  have hIBP1 :
      H3FirstDerivativeTransportIntegrationByPartsAt
        u t :=
    h3FirstDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass
      ht
      hH3
      hGradient

  have hIBP2 :
      H3SecondDerivativeTransportIntegrationByPartsAt
        u t :=
    h3SecondDerivativeTransportIntegrationByPartsAt_of_energyClass
      hClass
      ht
      hH3
      hGradient

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

  have hAnalyticCore3 :
      H3OrderThreeInterpolationLandauCoreAnalyticDataAt
        u h t := by
    simpa [H3OrderThreeInterpolationLandauCoreAnalyticDataAt] using
      hGradient

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

  have hPDEInt :
      ∃ p :
          PrimeTensor.SpaceTimeScalarField
            ℝ ℝ ℝ Depth.three,
        H3PDEPairingIntegrableAt
          u p t := by
    rcases hData.2.2 with
      ⟨p, hNS, hAnalytic⟩

    exact
      ⟨
        p,
        (hAnalytic t ht).2.2.1
      ⟩

  rcases hPDEInt with
    ⟨pEnergy, hPDEPairing⟩

  have hPairing3 :
      H3OrderThreeTransportPairingIntegrableAt
        u t :=
    h3OrderThreeTransportPairingIntegrableAt_of_pde
      hClass
      ht
      hPDEPairing
      hGradientPairing3
      hInterpolationPairing3

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
