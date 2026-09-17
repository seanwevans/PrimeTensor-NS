import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyGlobalClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureJoint

/-!
# Replace the old-pressure mass frontier by pressure-gradient joint continuity

The derivative-free weak-energy route has reduced the entire endpoint
continuity problem to the previously isolated old-pressure mass frontier.

`TemporalPressureJoint` already proves that a more structural condition implies
that mass frontier:

    joint continuity of (t,x) ↦ ∂ᵢ p_old(t,x)
      -> uniform compact-test pressure-gradient mass.

Composing that result with the weak-energy closure yields:

* weighted H³ spectral-state continuity;
* the complete ordered-third physical `L²` continuity frontier; and
* the global continuation target

from the single pressure-gradient joint-continuity frontier.

This file adds no new analytic assumption beyond the named structural frontier;
it only makes the final dependency exact.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyPressureJointClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Pressure-gradient joint continuity forces global weighted-H³ spectral-state
continuity through the old-pressure mass estimate and weak-energy uniqueness. -/
theorem h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_pressureJointWeakEnergy
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointContinuityFrontier) :
    H3PreterminalTailUnitViscositySpectralContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscositySpectralContinuityFrontier_of_oldPressureWeakEnergy
      (h3PreterminalTailUnitViscosityZeroOldPressureFrontier_of_pressureJoint
        hJoint)

/-- Hence pressure-gradient joint continuity also forces the complete
ordered-third physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_pressureJointWeakEnergy
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointContinuityFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_oldPressureWeakEnergy
      (h3PreterminalTailUnitViscosityZeroOldPressureFrontier_of_pressureJoint
        hJoint)

/-- The endpoint weak--strong uniqueness route is therefore completely closed
once the old preterminal pressure gradient is jointly continuous in spacetime. -/
theorem h3ControlProducesExtension_of_pressureJointWeakEnergyClosed
    (hJoint :
      H3PreterminalPressureFirstSpatialDerivativeJointContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureWeakEnergyClosed
      (h3PreterminalTailUnitViscosityZeroOldPressureFrontier_of_pressureJoint
        hJoint)

end

end Euclidean
end Bridge
end PrimeTensor
