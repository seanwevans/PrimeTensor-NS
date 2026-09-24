import PrimeTensor.Fluid.Vorticity.Continuation.H3.Analysis.Closed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Majorant.Only

/-!
# Split the remaining H³-path analytic frontier

`H3PathAnalyticOnly` reduced the H³-path BKM theorem to one remaining package:

    H3EnergyEstimateAnalyticOnTail.

That package still mixes two logically independent analytic problems.

## Time differentiation

The exact identities

    d/dt ∫ |D^α u|²
      =
    2 ∫ D^αu D^α∂ₜu

for `|α| ≤ 3`.

The existing endpoint-continuity development has already reduced this side to

* explicit PDE-form second/third time derivatives;
* locally uniform integrable spatial majorants.

All square and derivative-product measurability has already been discharged.

## Spatial whole-space analysis

At each fixed strict tail time:

* higher momentum split regularity;
* PDE pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

This file separates those fronts and proves that their conjunction reconstructs
`H3EnergyEstimateAnalyticOnTail`.

Consequently the H³-path BKM theorem can be stated with the concrete derivative
frontiers already developed elsewhere, plus one purely spatial whole-space
frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/--
The fixed-time spatial part of the canonical H³ energy analysis on an
H³-path-admissible high-order tail.

The derivative-under-integral identities are deliberately absent.
-/
def H3PathEnergyClassProducesSpatialAnalyticTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∃ p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three,
            PreterminalNavierStokes3
                (logSpaceTimeVectorField u)
                p
                T
              ∧
            ∀ t : ℝ,
              t ∈ Set.Ioo a T →
                HigherOrderMomentumSplitRegularityAt
                    (logSpaceTimeVectorField u)
                    p
                    t
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
Tail-local derivative inputs plus the fixed-time spatial package reconstruct
the complete analytic energy tail on every H³ path.
-/
theorem h3PathEnergyClassProducesAnalyticTail_of_derivativeInputs_of_spatial
    (hDerivative :
      EnergyClassProducesH3EnergyDerivativeTailLocalInputs)
    (hSpatial :
      H3PathEnergyClassProducesSpatialAnalyticTail) :
    H3PathEnergyClassProducesAnalyticTail := by

  intro u T hH3 a hClass

  rcases
    hDerivative u a T hClass
  with
    ⟨
      hMixed2,
      hMixed3,
      hLocalDom
    ⟩

  rcases
    hSpatial u T hH3 a hClass
  with
    ⟨
      p,
      hPDE,
      hSpatialTail
    ⟩

  refine
    ⟨
      p,
      hPDE,
      ?_
    ⟩

  intro t ht

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 ht.1,
        ht.2
      ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  rcases hLocalDom t ht with
    ⟨hDom⟩

  have hDerivativeAt :
      H3OrderEnergyDerivativeIdentities
        u t :=
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
      hH3.navier_stokes
      htAbs
      hInt
      hMixed2
      hMixed3
      hDom

  rcases hSpatialTail t ht with
    ⟨
      hRegular,
      hPairing,
      hPressure,
      hDiffusion
    ⟩

  exact
    ⟨
      hDerivativeAt,
      hRegular,
      hPairing,
      hPressure,
      hDiffusion
    ⟩

/--
The explicit higher-time PDE frontier and tail-local domination frontier
reconstruct the derivative half, leaving only the fixed-time spatial package.
-/
theorem h3PathEnergyClassProducesAnalyticTail_of_pdeTime_of_domination_of_spatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination)
    (hSpatial :
      H3PathEnergyClassProducesSpatialAnalyticTail) :
    H3PathEnergyClassProducesAnalyticTail := by

  exact
    h3PathEnergyClassProducesAnalyticTail_of_derivativeInputs_of_spatial
      (energyClassProducesH3EnergyDerivativeTailLocalInputs_of_pde_of_domination
        hTime
        hDom)
      hSpatial

/--
After the already-proved measurability reductions, locally uniform integrable
majorants are enough to discharge the domination side.
-/
theorem h3PathEnergyClassProducesAnalyticTail_of_pdeTime_of_majorants_of_spatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesSpatialAnalyticTail) :
    H3PathEnergyClassProducesAnalyticTail := by

  have hReduced :
      EnergyClassProducesH3EnergyDerivativeReducedDomination :=
    energyClassProducesH3EnergyDerivativeReducedDomination_of_majorants
      hMajorants

  have hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination :=
    energyClassProducesH3EnergyDerivativeTailLocalDomination_of_reduced
      hReduced

  exact
    h3PathEnergyClassProducesAnalyticTail_of_pdeTime_of_domination_of_spatial
      hTime
      hDom
      hSpatial

/--
H³-path BKM control with the remaining energy analysis split into concrete
time-differentiation and fixed-time whole-space fronts.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_spatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesSpatialAnalyticTail) :
    H3PathVorticityL1LinfProducesH3Control := by

  exact
    h3PathVorticityL1LinfProducesH3Control_of_analyticTail
      (h3PathEnergyClassProducesAnalyticTail_of_pdeTime_of_majorants_of_spatial
        hTime
        hMajorants
        hSpatial)

/--
H³-path BKM continuation at the newly split analytic frontier.

The continuation, logarithmic endpoint, scalar Osgood step, path continuity,
H³ integrability, derivative-product measurability, and nearby square
measurability are all closed.

The remaining inputs are now explicit:

1. higher PDE time differentiability;
2. locally uniform integrable derivative majorants;
3. fixed-time whole-space pairing / pressure-IBP / diffusion-IBP analysis.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_spatial
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hSpatial :
      H3PathEnergyClassProducesSpatialAnalyticTail) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_analyticTail
      (h3PathEnergyClassProducesAnalyticTail_of_pdeTime_of_majorants_of_spatial
        hTime
        hMajorants
        hSpatial)

end

end Euclidean
end Bridge
end PrimeTensor
