import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Product
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Mixed.Closed.PDE.Closure

/-!
# Close unit-viscosity continuation from product integrability alone

`Physical.Tail.Unit.Viscosity.Frontier.Product` proves that the global temporal
product-integrability frontier implies the existing unit-viscosity
physical-tail evolution frontier.

Independently, `Selected.Mixed.Closed.PDE.Closure` has already closed the entire
selected-side local PDE remainder: unit-viscosity physical-tail evolution alone
implies `H3ControlProducesExtension`.

Therefore the local PDE/pressure frontier carried by the earlier product
wrapper is no longer needed for the continuation target.

This file records the final composition:

    product integrability
      -> physical-tail evolution
      -> selected mixed/PDE closure
      -> H3ControlProducesExtension.

No new analytic estimate, PDE identity, gluing argument, or regularity theorem is
introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- The global unit-viscosity temporal product-integrability frontier alone
implies the original H³ continuation target. -/
theorem h3ControlProducesExtension_of_unitViscosityProductIntegrability
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontier) :
    H3ControlProducesExtension := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityProductIntegrabilityFrontier
      hProduct

  exact
    h3ControlProducesExtension_of_unitViscositySelectedMixedClosedPDE
      hEvolution

end

end Euclidean
end Bridge
end PrimeTensor
