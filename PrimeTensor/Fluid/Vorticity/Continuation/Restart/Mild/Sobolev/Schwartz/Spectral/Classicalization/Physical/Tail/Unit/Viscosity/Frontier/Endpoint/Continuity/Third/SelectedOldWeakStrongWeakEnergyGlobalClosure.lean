import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyRestartRadius
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SpectralContinuity

/-!
# Global closure of the weak-energy uniqueness route

The derivative-free weak-energy argument has now been lifted across the entire
canonical restart radius under the already-isolated old-pressure frontier.

That local result is exactly the input required by the existing global weighted
H³ spectral continuity frontier.  Therefore:

* the old-pressure frontier implies global weighted H³ spectral-state
  continuity;
* hence it implies the complete ordered-third physical `L²` continuity
  frontier;
* the zeroth branch was already known to follow from the same old-pressure
  frontier;
* consequently the current continuation theorem needs no independent
  third-order continuity assumption.

At this stage the endpoint-continuity/weak--strong uniqueness branch has been
collapsed to the single previously isolated global old-pressure mass frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyGlobalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The existing global old-pressure frontier now forces global weighted-H³
spectral-state continuity through derivative-free weak-energy uniqueness. -/
theorem h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressureWeakEnergy
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscositySpectralContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  have hOldRadius :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hOld E hE u T t hNS ht hTail

  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_oldPressureWeakEnergy
      (tau := (q : ℝ))
      hNS
      ht
      hqPos
      hEnd
      hE
      hTail
      q.property.2
      hOldRadius

/-- Hence the same old-pressure frontier forces the complete global
ordered-third physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_oldPressureWeakEnergy
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_spectral
      (h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressureWeakEnergy
        hOld)

/-- Global continuation closure with the endpoint weak--strong uniqueness route
discharged: the previously isolated old-pressure mass frontier alone supplies
both zeroth and ordered-third endpoint continuity. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureWeakEnergyClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSpectralContinuityClosed
      hOld
      (h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressureWeakEnergy
        hOld)

end

end Euclidean
end Bridge
end PrimeTensor
