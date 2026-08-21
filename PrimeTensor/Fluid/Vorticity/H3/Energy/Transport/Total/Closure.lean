import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Cancellation
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.One.Total.Bound
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Two.Total.Bound
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Landau.Closure

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
The third-order energy is one nonnegative summand of the normalized canonical
H³ energy.
-/
theorem velocityH3Energy3At_le_velocityH3EnergyAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    velocityH3Energy3At u t
      ≤
    velocityH3EnergyAt u t := by

  have h0 :
      0 ≤ velocityH3Energy0At u t :=
    velocityH3Energy0At_nonneg u t

  have h1 :
      0 ≤ velocityH3Energy1At u t :=
    velocityH3Energy1At_nonneg u t

  have h2 :
      0 ≤ velocityH3Energy2At u t :=
    velocityH3Energy2At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

/--
Complete canonical H³ transport closure.

The four derivative orders contribute

* order zero: `0`, by whole-space kinetic-energy flux cancellation;
* order one: `6 h(t) E_H3(t)`;
* order two: `18 h(t) E_H3(t)`;
* order three: `4398 h(t) E₃(t) ≤ 4398 h(t) E_H3(t)`.

Hence

    |T_H3(t)| ≤ 4422 h(t) E_H3(t).
-/
theorem velocityH3TransportDerivativeAt_le_of_landauAnalyticData
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
    abs
        (
          velocityH3TransportDerivativeAt
            u t
        )
      ≤
    4422 * h t * velocityH3EnergyAt u t := by

  have hGradient :
      VelocityGradientEnvelope
        u h t :=
    hAnalytic.2.1

  have h0 :
      velocityH3TransportDerivative0At u t = 0 :=
    velocityH3TransportDerivative0At_eq_zero_of_energyClass
      hClass
      ht
      hFlux0

  have h1 :
      abs (velocityH3TransportDerivative1At u t)
        ≤ 6 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative1At_le_totalEnergy
      hClass
      ht
      hFlux1
      hPairing1
      hH3
      hGradient

  have h2 :
      abs (velocityH3TransportDerivative2At u t)
        ≤ 18 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivative2At_le_totalEnergy
      hClass
      ht
      hFlux2
      hPairing2
      hH3
      hGradient

  have h3 :
      abs (velocityH3TransportDerivative3At u t)
        ≤ 4398 * h t * velocityH3Energy3At u t :=
    velocityH3TransportDerivative3At_le_of_landauAnalyticData
      hClass
      ht
      hRegular3
      hFlux3
      hPairing3
      hGradientPairing3
      hH3
      hAnalytic

  have hEnvelope :
      0 ≤ h t :=
    velocityGradientEnvelope_nonneg
      hGradient
      (
        fun _ =>
          (0 : ℝ)
      )

  have hEnergy3 :
      velocityH3Energy3At u t
        ≤ velocityH3EnergyAt u t :=
    velocityH3Energy3At_le_velocityH3EnergyAt
      u t

  have hCoeff :
      0 ≤ (4398 : ℝ) * h t := by
    positivity

  have h3Total :
      abs (velocityH3TransportDerivative3At u t)
        ≤ 4398 * h t * velocityH3EnergyAt u t := by
    exact
      le_trans
        h3
        (
          mul_le_mul_of_nonneg_left
            hEnergy3
            hCoeff
        )

  have hTriangle :
      abs
          (
            velocityH3TransportDerivative1At u t
              + velocityH3TransportDerivative2At u t
              + velocityH3TransportDerivative3At u t
          )
        ≤
      abs (velocityH3TransportDerivative1At u t)
        + abs (velocityH3TransportDerivative2At u t)
        + abs (velocityH3TransportDerivative3At u t) := by
    calc
      abs
          (
            velocityH3TransportDerivative1At u t
              + velocityH3TransportDerivative2At u t
              + velocityH3TransportDerivative3At u t
          )
        ≤
      abs
          (
            velocityH3TransportDerivative1At u t
              + velocityH3TransportDerivative2At u t
          )
        + abs (velocityH3TransportDerivative3At u t) := by
          exact abs_add_le _ _
      _ ≤
      (
        abs (velocityH3TransportDerivative1At u t)
          + abs (velocityH3TransportDerivative2At u t)
      )
        + abs (velocityH3TransportDerivative3At u t) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right
              (
                abs_add_le
                  (velocityH3TransportDerivative1At u t)
                  (velocityH3TransportDerivative2At u t)
              )
              (abs (velocityH3TransportDerivative3At u t))

  have hSum :
      abs (velocityH3TransportDerivative1At u t)
        + abs (velocityH3TransportDerivative2At u t)
        + abs (velocityH3TransportDerivative3At u t)
        ≤
      4422 * h t * velocityH3EnergyAt u t := by
    nlinarith [h1, h2, h3Total]

  unfold velocityH3TransportDerivativeAt
  rw [h0]
  norm_num
  exact le_trans hTriangle hSum


/--
The concrete `4422 h(t) E_H3(t)` transport estimate discharges the older
abstract commutator interface with the universal coefficient `4422`.

The abstract interface uses `4422 * (1 + |h(t)|) * E_H3(t)`, so the passage is
only the elementary inequality

    h(t) ≤ 1 + |h(t)|,

together with nonnegativity of the canonical H³ energy.
-/
theorem h3TransportCommutatorBoundAt_of_landauAnalyticData
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
    H3TransportCommutatorBoundAt
      u h 4422 t := by

  have hTransport :
      abs (velocityH3TransportDerivativeAt u t)
        ≤ 4422 * h t * velocityH3EnergyAt u t :=
    velocityH3TransportDerivativeAt_le_of_landauAnalyticData
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

  have hGradient :
      VelocityGradientEnvelope
        u h t :=
    hAnalytic.2.1

  have hh :
      0 ≤ h t :=
    velocityGradientEnvelope_nonneg
      hGradient
      (
        fun _ =>
          (0 : ℝ)
      )

  have hEnergyOne :
      1 ≤ velocityH3EnergyAt u t :=
    one_le_velocityH3EnergyAt u t

  have hEnergy :
      0 ≤ velocityH3EnergyAt u t := by
    linarith

  unfold H3TransportCommutatorBoundAt

  have hEnvelope :
      h t ≤ 1 + |h t| := by
    rw [abs_of_nonneg hh]
    linarith

  have hScale :
      0 ≤ (4422 : ℝ) := by
    norm_num

  have hRight :
      4422 * h t * velocityH3EnergyAt u t
        ≤
      4422 * (1 + |h t|) * velocityH3EnergyAt u t := by
    nlinarith

  exact le_trans hTransport hRight


end Euclidean
end Bridge
end PrimeTensor
