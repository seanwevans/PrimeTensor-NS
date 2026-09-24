import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Pointwise.Frontier

/-!
# Remove the automatic RHS split from the H³-path spatial frontier

`H3PathPointwiseEnergyFrontier` lowered the spatial side of the H³ energy
argument to exact fixed-time data:

* higher-order momentum RHS splits;
* PDE pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

The first item is not a remaining analytic hypothesis.

For every `PreterminalH3EnergyClass` and every strict tail time,
`preterminalH3EnergyClass_produces_momentumRHSSplits` already constructs a
pressure witness satisfying the exact higher-order RHS split.

This file chooses that witness once and states the remaining spatial frontier
only for the three whole-space facts which are not already theorem-level
consequences of the class:

* PDE pairing integrability;
* pressure integration by parts;
* diffusion integration by parts.

Thus the H³-path BKM theorem no longer carries any momentum-split hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-! ## Canonical split pressure at one tail time -/

/--
The pressure witness selected from the already-proved exact momentum-split
theorem.
-/
noncomputable def h3EnergyClassSplitPressureAt
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  Classical.choose
    (preterminalH3EnergyClass_produces_momentumRHSSplits
      hClass ht)

/--
The selected split pressure is an actual pressure witness for the old
preterminal Navier--Stokes solution.
-/
theorem h3EnergyClassSplitPressureAt_navierStokes
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    PreterminalNavierStokes3
      (logSpaceTimeVectorField u)
      (h3EnergyClassSplitPressureAt hClass ht)
      T := by
  exact
    (Classical.choose_spec
      (preterminalH3EnergyClass_produces_momentumRHSSplits
        hClass ht)).1

/--
The selected split pressure carries the exact higher-order RHS split.
-/
theorem h3EnergyClassSplitPressureAt_momentumRHSSplits
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T t : ℝ}
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    HigherOrderMomentumRHSSplitsAt
      (logSpaceTimeVectorField u)
      (h3EnergyClassSplitPressureAt hClass ht)
      t := by
  exact
    (Classical.choose_spec
      (preterminalH3EnergyClass_produces_momentumRHSSplits
        hClass ht)).2

/-! ## Genuine remaining fixed-time whole-space frontier -/

/--
The remaining fixed-time whole-space H³ energy analysis.

Momentum splitting is absent because it is already automatic from the energy
class.  The only spatial hypotheses retained are the integral facts which
require genuine whole-space control.
-/
def H3PathEnergyClassProducesWholeSpaceEnergyData : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        ∀ hClass : PreterminalH3EnergyClass u a T,
          ∀ t : ℝ,
            ∀ ht : t ∈ Set.Ioo a T,
              H3PDEPairingIntegrableAt
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                ∧
              H3PressureIntegrationByPartsAt
                  u
                  (h3EnergyClassSplitPressureAt hClass ht)
                  t
                ∧
              H3DiffusionIntegrationByPartsAt
                  u t

/--
The whole-space frontier reconstructs the previous pointwise spatial package;
the pressure witness and RHS split are supplied automatically.
-/
theorem h3PathEnergyClassProducesPointwiseSpatialEnergyData_of_wholeSpace
    (hWhole :
      H3PathEnergyClassProducesWholeSpaceEnergyData) :
    H3PathEnergyClassProducesPointwiseSpatialEnergyData := by

  intro u T hH3 a hClass t ht

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3EnergyClassSplitPressureAt hClass ht

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_navierStokes
        hClass ht

  have hSplit :
      HigherOrderMomentumRHSSplitsAt
        (logSpaceTimeVectorField u)
        p
        t := by
    dsimp only [p]
    exact
      h3EnergyClassSplitPressureAt_momentumRHSSplits
        hClass ht

  rcases hWhole u T hH3 a hClass t ht with
    ⟨hPairing, hPressure, hDiffusion⟩

  refine
    ⟨
      p,
      hPDE,
      hSplit,
      ?_,
      ?_,
      hDiffusion
    ⟩

  · simpa only [p] using hPairing
  · simpa only [p] using hPressure

/-! ## BKM closure at the genuine whole-space frontier -/

/--
Terminal H³ control with exact momentum splitting removed from the free
spatial assumptions.
-/
theorem h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_wholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesH3Control := by

  exact
    h3PathVorticityL1LinfProducesH3Control_of_pdeTime_of_majorants_of_pointwiseSpatial
      hTime
      hMajorants
      (h3PathEnergyClassProducesPointwiseSpatialEnergyData_of_wholeSpace
        hWhole)

/--
H³-path BKM continuation at the reduced whole-space energy frontier.

The remaining explicit inputs are now exactly:

1. higher PDE time differentiability;
2. locally uniform integrable derivative majorants;
3. PDE pairing integrability;
4. pressure integration by parts;
5. diffusion integration by parts.

The last three are grouped in
`H3PathEnergyClassProducesWholeSpaceEnergyData`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_wholeSpace
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hWhole :
      H3PathEnergyClassProducesWholeSpaceEnergyData) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_pdeTime_of_majorants_of_pointwiseSpatial
      hTime
      hMajorants
      (h3PathEnergyClassProducesPointwiseSpatialEnergyData_of_wholeSpace
        hWhole)

end

end Euclidean
end Bridge
end PrimeTensor
