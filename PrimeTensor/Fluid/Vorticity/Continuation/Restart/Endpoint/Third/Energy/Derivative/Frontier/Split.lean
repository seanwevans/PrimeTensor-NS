import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Assembly

/-!
# Split the remaining H³ energy-derivative frontier

`EnergyDerivativeAssembly` reduced pressure-free continuation to one bundled
tail input.  That bundle contains two analytically different obligations:

1. higher mixed time/space commutation for orders two and three;
2. whole-space local domination needed to exchange time differentiation with
   the H³ square integrals.

These should not be hidden inside one proposition.  This file separates them
and proves that their conjunction reconstructs the assembled tail input and
therefore still yields the complete continuation theorem.

This makes the remaining PDE work explicit:

    smoothing into the H³ energy class
      +
    higher mixed-time regularity
      +
    differentiation-under-integral domination
      =>
    pressure-free continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Energy-class solutions possess the two higher mixed time/space derivative
commutation witnesses needed by the order-two and order-three H³ blocks. -/
def EnergyClassProducesH3MixedTimeRegularity : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        H3Order2VelocityMixedTimeDerivativeOnPreterminal u T
          ∧
        H3Order3VelocityMixedTimeDerivativeOnPreterminal u T

/-- Energy-class solutions possess the local whole-space domination data needed
to differentiate all four H³ square-energy blocks.

Square integrability itself is deliberately not included here; the late
continuation argument already gets that from `TerminalTailH3Control`. -/
def EnergyClassProducesH3EnergyDerivativeDomination : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeDominationDataAt u T t)

/-- The split mixed-time and domination frontiers reconstruct the bundled tail
input used by `EnergyDerivativeAssembly`. -/
theorem energyClassProducesH3EnergyDerivativeTailInputs_of_split
    (hMixed : EnergyClassProducesH3MixedTimeRegularity)
    (hDom : EnergyClassProducesH3EnergyDerivativeDomination) :
    EnergyClassProducesH3EnergyDerivativeTailInputs := by
  intro u a T hClass

  rcases hMixed u a T hClass with
    ⟨hMixed2, hMixed3⟩

  exact
    ⟨
      hMixed2,
      hMixed3,
      hDom u a T hClass
    ⟩

/-- Real restart from smoothing plus the two separated derivative frontiers. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeSplit
    (hSmooth : H3SeedProducesEnergyClass)
    (hMixed : EnergyClassProducesH3MixedTimeRegularity)
    (hDom : EnergyClassProducesH3EnergyDerivativeDomination) :
    H3ControlProducesRealRestart := by
  exact
    h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailInputs
      hSmooth
      (energyClassProducesH3EnergyDerivativeTailInputs_of_split
        hMixed
        hDom)

/-- Pressure-free continuation from smoothing plus the exact two remaining
energy-derivative obligations. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeSplit
    (hSmooth : H3SeedProducesEnergyClass)
    (hMixed : EnergyClassProducesH3MixedTimeRegularity)
    (hDom : EnergyClassProducesH3EnergyDerivativeDomination) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailInputs
      hSmooth
      (energyClassProducesH3EnergyDerivativeTailInputs_of_split
        hMixed
        hDom)

end

end Euclidean
end Bridge
end PrimeTensor
