import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Evolution.Vorticity

/-!
# Unit-viscosity continuation frontier after the vorticity closure

The vorticity route has eliminated the temporal product-integrability frontier
from physical-tail evolution.  At each retained canonical H³ tail, radius-wide
physical evolution now follows from endpoint physical `L²` continuity alone.

The established unit-viscosity continuation theorem is stated in terms of the
older abstract physical-evolution frontier.  This file bridges the new reduced
interface to that theorem:

1. a global radius-wide endpoint-continuity frontier implies the existing
   unit-viscosity physical-evolution frontier;
2. together with the already-isolated local normalized PDE/pressure frontier,
   this yields the complete real restart theorem; and
3. therefore it yields `H3ControlProducesExtension`.

No temporal product-integrability, weak temporal derivative, restart, gluing,
pressure, spatial-regularity, or terminal-jet argument is reproved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Global unit-viscosity endpoint physical `L²` continuity frontier for every
retained canonical H³ tail.

At each retained tail this is exactly the radius-wide continuity-only frontier
introduced in `Physical.Tail.Evolution.Vorticity`. -/
def H3PreterminalTailUnitViscosityEndpointContinuityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global endpoint-continuity frontier implies the existing
unit-viscosity strong/mild physical-tail evolution frontier. -/
theorem h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityEndpointContinuityFrontier
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontier) :
    H3PreterminalTailPhysicalEvolutionFrontier
      (1 : ℝ)
      (one_pos : (0 : ℝ) < 1) := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS
      ht
      hE
      hTail
      (hContinuity E hE u T t hNS ht hTail)

/-- The global endpoint-continuity frontier plus the remaining local
unit-viscosity PDE/pressure frontier imply the complete real H³ restart
theorem. -/
theorem h3ControlProducesRealRestart_of_unitViscosityEndpointContinuityFrontier
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontier)
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesRealRestart := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityEndpointContinuityFrontier
      hContinuity

  exact
    h3ControlProducesRealRestart_of_unitViscosityPhysicalTailFrontiers
      hEvolution
      hLocalPDE

/-- Consequently, radius-wide endpoint physical `L²` continuity of the old H³
tail, together with the remaining local normalized PDE/pressure frontier,
implies the original H³ continuation target. -/
theorem h3ControlProducesExtension_of_unitViscosityEndpointContinuityFrontier
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontier)
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesExtension := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityEndpointContinuityFrontier
      hContinuity

  exact
    h3ControlProducesExtension_of_unitViscosityPhysicalTailFrontiers
      hEvolution
      hLocalPDE

end

end Euclidean
end Bridge
end PrimeTensor
