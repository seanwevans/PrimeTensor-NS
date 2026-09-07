import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Evolution.Product

/-!
# Unit-viscosity continuation frontier from temporal product integrability

`Physical.Tail.Evolution.Product` packages the new temporal
product-integrability route over the complete unit-viscosity restart radius.

The established unit-viscosity continuation theorem, however, is stated in
terms of the older abstract physical-evolution frontier.

This file bridges those two interfaces:

1. a global radius-wide product-integrability frontier implies the existing
   unit-viscosity physical-evolution frontier;
2. together with the already-isolated local normalized PDE/pressure frontier,
   this yields the complete real restart theorem; and
3. therefore it yields `H3ControlProducesExtension`.

No restart, gluing, pressure, spatial-regularity, or terminal-jet argument is
reproved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Global unit-viscosity temporal product-integrability frontier for every
retained canonical H³ tail.

At each retained tail this is exactly the radius-wide frontier introduced in
`Physical.Tail.Evolution.Product`. -/
def H3PreterminalTailUnitViscosityProductIntegrabilityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global product-integrability frontier implies the existing
unit-viscosity strong/mild physical-tail evolution frontier. -/
theorem h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityProductIntegrabilityFrontier
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontier) :
    H3PreterminalTailPhysicalEvolutionFrontier
      (1 : ℝ)
      (one_pos : (0 : ℝ) < 1) := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_all_productIntegrable
      hNS
      ht
      hE
      hTail
      (hProduct E hE u T t hNS ht hTail)

/-- The global product-integrability frontier plus the remaining local
unit-viscosity PDE/pressure frontier imply the complete real H³ restart
theorem. -/
theorem h3ControlProducesRealRestart_of_unitViscosityProductIntegrabilityFrontier
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontier)
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesRealRestart := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityProductIntegrabilityFrontier
      hProduct

  exact
    h3ControlProducesRealRestart_of_unitViscosityPhysicalTailFrontiers
      hEvolution
      hLocalPDE

/-- Consequently, temporal product integrability for the old H³ tail, together
with the remaining local normalized PDE/pressure frontier, implies the original
H³ continuation target. -/
theorem h3ControlProducesExtension_of_unitViscosityProductIntegrabilityFrontier
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontier)
    (hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEFrontier) :
    H3ControlProducesExtension := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1) :=
    h3PreterminalTailPhysicalEvolutionFrontier_of_unitViscosityProductIntegrabilityFrontier
      hProduct

  exact
    h3ControlProducesExtension_of_unitViscosityPhysicalTailFrontiers
      hEvolution
      hLocalPDE

end

end Euclidean
end Bridge
end PrimeTensor
