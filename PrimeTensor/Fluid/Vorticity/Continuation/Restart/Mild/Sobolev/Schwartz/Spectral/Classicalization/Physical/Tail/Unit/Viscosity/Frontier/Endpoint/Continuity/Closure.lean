import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Split
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Mixed.Closed.PDE.Closure

/-!
# Closure of the unit-viscosity continuation frontier

The vorticity route reduced physical-tail evolution to radius-wide endpoint
physical `L²` continuity.  The split frontier then separated that endpoint
condition into zeroth-order and ordered-third-order continuity.

An older bridge still carried a separate local PDE/pressure frontier.  That
frontier is no longer genuinely open: `Selected.Mixed.Closed.PDE.Closure`
already proves that unit-viscosity physical-tail evolution alone supplies the
canonical local pressure, mixed regularity, incompressibility, momentum
equation, and a restart endpoint crossing the old terminal time.

Therefore the continuation boundary can now be closed one step further:

    endpoint physical L² continuity
      -> physical-tail evolution
      -> H3ControlProducesExtension.

Equivalently, after the preceding split, the only remaining hypotheses at this
level are the zeroth-order and ordered-third-order physical `L²` continuity
frontiers.

No PDE, pressure, mixed-derivative, incompressibility, momentum, gluing, or
endpoint-selection hypothesis remains in this interface.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

/-- Radius-wide unit-viscosity endpoint physical `L²` continuity alone implies
the original H³ continuation target.

The endpoint-continuity frontier first gives the physical-tail evolution
frontier through the vorticity bridge.  The already-closed selected mixed PDE
chain then supplies the complete local real continuation package. -/
theorem h3ControlProducesExtension_of_unitViscosityEndpointContinuityClosed
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontier) :
    H3ControlProducesExtension := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityEndpointContinuityFrontier
      hContinuity

  exact
    h3ControlProducesExtension_of_unitViscositySelectedMixedClosedPDE
      hEvolution

/-- Split form of the closed unit-viscosity continuation frontier.

After all downstream PDE-side closure work already present in the repository,
the original H³ continuation target follows from exactly the two time-topology
halves isolated by `Endpoint.Continuity.Split`: zeroth-order physical `L²`
continuity and ordered-third-order physical `L²` continuity. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroThirdContinuityClosed
    (hZero :
      H3PreterminalTailUnitViscosityZeroContinuityFrontier)
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityEndpointContinuityClosed
      (h3PreterminalTailUnitViscosityEndpointContinuityFrontier_of_zero_third
        hZero hThird)

end

end Euclidean
end Bridge
end PrimeTensor
