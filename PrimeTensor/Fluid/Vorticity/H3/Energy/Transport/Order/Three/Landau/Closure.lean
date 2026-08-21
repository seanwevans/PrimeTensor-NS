import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Monomials
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Direct.Closure
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Pairing.Integrability

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The complete third-order transport contribution is controlled once the
gradient branch and the Landau/Hölder interpolation branch are both available.

The constant is left factored here to record its provenance:

* `24` from the gradient block;
* `4374 = 729 * 6` from the interpolation block.
-/
theorem velocityH3TransportDerivative3At_le_of_landauAnalyticData_factored
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {a T t : ℝ}
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    )
    (
      hGradPairing :
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
    abs
        (
          velocityH3TransportDerivative3At
            u t
        )
      ≤
    (24 + 4374) * h t * velocityH3Energy3At u t := by
  have hMonomialPairing :
      H3OrderThreeInterpolationMonomialPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationMonomialPairingIntegrableAt_of_landauAnalyticData
      hAnalytic

  have hInterpPairing :
      H3OrderThreeInterpolationPairingIntegrableAt
        u t :=
    h3OrderThreeInterpolationPairingIntegrableAt_of_monomials
      hMonomialPairing

  have hInterp :
      H3OrderThreeInterpolationEstimateAt
        u h t 4374 :=
    h3OrderThreeInterpolationEstimateAt_of_landauAnalyticData
      hMonomialPairing
      hAnalytic

  exact
    velocityH3TransportDerivative3At_le_of_interpolation
      hClass
      ht
      hRegular
      hFlux
      hPairing
      hGradPairing
      hInterpPairing
      hH3
      hAnalytic.2.1
      hInterp

/--
Numerical form of
`velocityH3TransportDerivative3At_le_of_landauAnalyticData_factored`.

The full third-order transport coefficient is `4398`.
-/
theorem velocityH3TransportDerivative3At_le_of_landauAnalyticData
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {a T t : ℝ}
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
      hRegular :
        H3OrderThreeTransportRegularityAt
          u t
    )
    (
      hFlux :
        H3ThirdDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderThreeTransportPairingIntegrableAt
          u t
    )
    (
      hGradPairing :
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
    abs
        (
          velocityH3TransportDerivative3At
            u t
        )
      ≤
    4398 * h t * velocityH3Energy3At u t := by
  have hBound :=
    velocityH3TransportDerivative3At_le_of_landauAnalyticData_factored
      hClass
      ht
      hRegular
      hFlux
      hPairing
      hGradPairing
      hH3
      hAnalytic
  norm_num at hBound
  exact hBound

end Euclidean
end Bridge
end PrimeTensor
