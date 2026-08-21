import PrimeTensor.Fluid.VorticityH3EnergyTransport

/-!
# Recombining the canonical H³ energy estimate

The scalar pieces are now separated:

* diffusion is nonpositive under `H3DiffusionIntegrationByPartsAt`;
* pressure vanishes under `H3PressureIntegrationByPartsAt` together with the
  differentiated incompressibility supplied by `PreterminalH3EnergyClass`;
* transport is controlled by `H3TransportCommutatorBoundAt`.

This file recombines those statements with the exact differentiated
Navier--Stokes identity.

The remaining analytic data are deliberately packaged rather than hidden:
differentiation under the integral, pairing integrability, higher-order split
regularity, and the two whole-space integration-by-parts packages.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
All still-analytic data needed on a terminal tail to turn the exact
differentiated Navier--Stokes decomposition into the canonical H³ growth
inequality.

The pressure witness is included existentially together with the preterminal
Navier--Stokes equations it satisfies.  At each strict tail time we then ask
for exactly the differentiation, split-regularity, integrability, pressure-IBP,
and diffusion-IBP facts used by the scalar decomposition.
-/
def H3EnergyEstimateAnalyticOnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop :=
  ∃
    p :
      PrimeTensor.SpaceTimeScalarField
        ℝ ℝ ℝ Depth.three,
      PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
        ∧
      ∀ t : ℝ,
        t ∈ Set.Ioo a T →
          H3OrderEnergyDerivativeIdentities
              u t
            ∧
          HigherOrderMomentumSplitRegularityAt
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              p t
            ∧
          H3PDEPairingIntegrableAt
              u p t
            ∧
          H3PressureIntegrationByPartsAt
              u p t
            ∧
          H3DiffusionIntegrationByPartsAt
              u t

/--
Pointwise canonical H³ growth estimate obtained by recombining the exact PDE
split with diffusion nonpositivity, pressure cancellation, and the transport
commutator bound.
-/
theorem deriv_velocityH3EnergyAt_le_of_energyClass
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
    {a T t A : ℝ}
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
      hTransport :
        H3TransportCommutatorBoundAt
          u h A t
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      ≤
    A
      * (1 + |h t|)
      * velocityH3EnergyAt u t := by

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          ht.1,
        ht.2
      ⟩

  have hSplit :
      deriv
          (velocityH3EnergyAt u)
          t
        =
      velocityH3DiffusionDerivativeAt u t
        -
      velocityH3TransportDerivativeAt u t
        -
      velocityH3PressureDerivativeAt u p t := by

    exact
      deriv_velocityH3EnergyAt_eq_diffusion_sub_transport_sub_pressure_of_spatialC1
        s
        htNS
        hDerivative
        hRegular
        hInt

  have hDiffusion :
      velocityH3DiffusionDerivativeAt
          u t
        ≤
      0 :=
    velocityH3DiffusionDerivativeAt_nonpos
      hDiffusionIBP

  have hPressure :
      velocityH3PressureDerivativeAt
          u p t
        =
      0 :=
    preterminalH3EnergyClass_pressureDerivative_eq_zero
      hClass
      ht
      hPressureIBP

  have hTransportUpper :
      -
        velocityH3TransportDerivativeAt
          u t
        ≤
      A
        * (1 + |h t|)
        * velocityH3EnergyAt u t :=
    neg_transport_le_of_commutatorBound
      hTransport

  rw [
    hSplit,
    hPressure
  ]

  linarith

/--
Tail-level canonical H³ growth inequality.

Once the exact analytic tail package and the nonlinear transport control are
available, the normalized canonical energy itself is a valid
`H3GradientGrowthInequalityFrom` profile.
-/
theorem h3GradientGrowthInequalityFrom_canonical
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T A : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hAnalytic :
        H3EnergyEstimateAnalyticOnTail
          u a T
    )
    (
      hTransport :
        H3TransportControlledOnTail
          u a T h A
    ) :
    H3GradientGrowthInequalityFrom
      a T h
      (velocityH3EnergyAt u)
      A := by

  rcases hAnalytic with
    ⟨
      p,
      s,
      hTail
    ⟩

  intro t ht

  rcases
      hTail t ht
    with
      ⟨
        hDerivative,
        hRegular,
        hInt,
        hPressureIBP,
        hDiffusionIBP
      ⟩

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
      (hTransport t ht).2

end Euclidean
end Bridge
end PrimeTensor
