import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwoSum

/-!
# Second-order H³ transport bound by the total canonical energy

The summed order-two transport estimate has already been reduced to

    |T₂(t)| ≤ 18 h(t) E₂(t).

This file performs the final bookkeeping step needed by the eventual total
transport-control theorem: the second-order energy is bounded by the normalized
canonical H³ energy,

    E₂(t) ≤ E_H3(t),

and the nonnegative gradient envelope preserves that inequality under
multiplication.

No new analytic estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The second-order component of the canonical H³ energy is bounded by the full
normalized H³ energy.
-/
theorem velocityH3Energy2At_le_velocityH3EnergyAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    velocityH3Energy2At u t
      ≤
    velocityH3EnergyAt u t := by

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h1 :=
    velocityH3Energy1At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

/--
The complete second-order H³ transport derivative is controlled by the total
canonical H³ energy:

    |T₂(t)| ≤ 18 h(t) E_H3(t).

This is only positivity bookkeeping on top of the already proved order-two
commutator estimate.
-/
theorem velocityH3TransportDerivative2At_le_totalEnergy
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
      hFlux :
        H3SecondDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderTwoTransportPairingIntegrableAt
          u t
    )
    (
      hH3 :
        VelocityH3IntegrableAt
          u t
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    ) :
    abs
        (
          velocityH3TransportDerivative2At
            u t
        )
      ≤
    18 * h t * velocityH3EnergyAt u t := by

  have hOrderTwo :=
    velocityH3TransportDerivative2At_le_gradientEnvelope
      hClass
      ht
      hFlux
      hPairing
      hH3
      hGradient

  have hEnvelope :
      0 ≤ h t := by

    exact
      le_trans
        (
          abs_nonneg
            (
              spatial3.d
                xAxis
                (loggedVelocityComponent u t xAxis)
                (
                  fun _ =>
                    (0 : ℝ)
                )
            )
        )
        (
          hGradient
            xAxis
            xAxis
            (
              fun _ =>
                (0 : ℝ)
            )
        )

  have hEnergy :
      velocityH3Energy2At u t
        ≤
      velocityH3EnergyAt u t :=
    velocityH3Energy2At_le_velocityH3EnergyAt
      u t

  have hScale :
      18 * h t * velocityH3Energy2At u t
        ≤
      18 * h t * velocityH3EnergyAt u t := by

    exact
      mul_le_mul_of_nonneg_left
        hEnergy
        (
          mul_nonneg
            (by norm_num)
            hEnvelope
        )

  exact
    le_trans
      hOrderTwo
      hScale

end Euclidean
end Bridge
end PrimeTensor
