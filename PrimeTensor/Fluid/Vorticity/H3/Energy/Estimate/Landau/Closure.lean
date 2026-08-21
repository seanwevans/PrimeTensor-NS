import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Total.Closure

/-!
# H³ energy growth from the concrete Landau transport closure

This file connects the explicit order-by-order transport estimate

    |T_H3(t)| ≤ 4422 h(t) E_H3(t)

to the pre-existing canonical H³ energy estimate.  The diffusion and pressure
parts are unchanged; the only replacement is that the formerly abstract
`H3TransportCommutatorBoundAt` hypothesis is now derived from the concrete
Landau analytic data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Pointwise canonical H³ growth estimate with the abstract transport hypothesis
replaced by the explicit Landau transport closure.

The coefficient is the concrete transport constant

    6 + 18 + 4398 = 4422.

The existing energy-estimate interface uses the slightly coarser envelope
factor `1 + |h(t)|`, so the conclusion retains that form.
-/
theorem deriv_velocityH3EnergyAt_le_of_landauAnalyticData
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {a T t : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hDerivative :
        H3OrderEnergyDerivativeIdentities
          u t
    )
    (
      hRegular :
        HigherOrderMomentumSplitRegularityAt
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t
    )
    (
      hInt :
        H3PDEPairingIntegrableAt
          u p t
    )
    (
      hPressureIBP :
        H3PressureIntegrationByPartsAt
          u p t
    )
    (
      hDiffusionIBP :
        H3DiffusionIntegrationByPartsAt
          u t
    )
    (
      hFlux0 :
        H3TransportEnergyFluxVanishesAt
          u t
    )
    (
      hFlux1 :
        H3FirstDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing1 :
        H3OrderOneTransportPairingIntegrableAt
          u t
    )
    (
      hFlux2 :
        H3SecondDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing2 :
        H3OrderTwoTransportPairingIntegrableAt
          u t
    )
    (
      hRegular3 :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux3 :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing3 :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    )
    (
      hGradientPairing3 :
        H3OrderThreeGradientPairingIntegrableAt
          u t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hAnalytic :
        H3OrderThreeInterpolationLandauAnalyticDataAt
          u h t
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      ≤
    4422
      * (1 + |h t|)
      * velocityH3EnergyAt u t := by

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
      hAnalytic

  exact
    deriv_velocityH3EnergyAt_le_of_energyClass
      hClass
      s
      ht
      hDerivative
      hRegular
      hInt
      hPressureIBP
      hDiffusionIBP
      hTransport

end Euclidean
end Bridge
end PrimeTensor
