import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderOneSum

/-!
# First-order H³ transport bound by the total canonical energy

The summed order-one transport estimate has already been reduced to

    |T₁(t)| ≤ 6 h(t) E₁(t).

This file performs the final bookkeeping step needed by the eventual total
transport-control theorem: the first-order energy is bounded by the normalized
canonical H³ energy,

    E₁(t) ≤ E_H3(t),

and the nonnegative gradient envelope preserves that inequality under
multiplication.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The first-order component of the canonical H³ energy is bounded by the full
normalized H³ energy.
-/
theorem velocityH3Energy1At_le_velocityH3EnergyAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) :
    velocityH3Energy1At u t
      ≤
    velocityH3EnergyAt u t := by

  have h0 :=
    velocityH3Energy0At_nonneg u t

  have h2 :=
    velocityH3Energy2At_nonneg u t

  have h3 :=
    velocityH3Energy3At_nonneg u t

  unfold velocityH3EnergyAt

  linarith

/--
The complete first-order H³ transport derivative is controlled by the total
canonical H³ energy:

    |T₁(t)| ≤ 6 h(t) E_H3(t).

No estimate beyond the already proved order-one commutator bound is introduced
here; this is only positivity bookkeeping.
-/
theorem velocityH3TransportDerivative1At_le_totalEnergy
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
        H3FirstDerivativeTransportFluxVanishesAt
          u t
    )
    (
      hPairing :
        H3OrderOneTransportPairingIntegrableAt
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
          velocityH3TransportDerivative1At
            u t
        )
      ≤
    6 * h t * velocityH3EnergyAt u t := by

  have hOrderOne :=
    velocityH3TransportDerivative1At_le_gradientEnvelope
      hClass
      ht
      hFlux
      hPairing
      hH3
      hGradient

  have hEnvelope :
      0 ≤ h t :=
    velocityGradientEnvelope_nonneg
      hGradient
      (
        fun _ =>
          (0 : ℝ)
      )

  have hEnergy :
      velocityH3Energy1At u t
        ≤
      velocityH3EnergyAt u t :=
    velocityH3Energy1At_le_velocityH3EnergyAt
      u t

  have hScale :
      6 * h t * velocityH3Energy1At u t
        ≤
      6 * h t * velocityH3EnergyAt u t := by

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
      hOrderOne
      hScale

end Euclidean
end Bridge
end PrimeTensor
