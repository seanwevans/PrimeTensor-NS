import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Mild.Product

/-!
# Radius-wide physical tail evolution from product integrability

`Endpoint.Canonical.Mild.Product` proves one local unit-viscosity physical
evolution package from:

* endpoint physical `L²` continuity; and
* temporal product integrability for every compact smooth divergence-free weak
  test on every shortened endpoint interval.

The existing radius-wide overlap machinery consumes
`H3PreterminalTailPhysicalEvolutionOnRestartRadius`.

This file packages the new local frontier over the full unit-viscosity restart
radius and derives that existing radius-wide proposition unchanged.  It then
feeds the result directly into the established selected-restart overlap theorem.

No overlap uniqueness, decoder, or selected-restart argument is reproved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEvolutionProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radius-wide unit-viscosity product-integrability frontier.

For every positive elapsed target in the canonical unit-viscosity restart
radius, and every proof that the old branch still exists through that target,
the frontier supplies:

1. the endpoint physical `L²` continuity witness used to construct the
   canonical endpoint path; and
2. product integrability for every divergence-free weak test on every shortened
   interval of that endpoint problem. -/
def H3PreterminalTailUnitViscosityProductIntegrabilityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        ∃ hEndpoint :
            H3PreterminalCanonicalL2EndpointContinuousOnElapsed
              hNS ht hEnd hTail,
          H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyProductIntegrableOnElapsed
            hNS ht hqPos hEnd hE hTail hEndpoint

/-- The radius-wide product-integrability frontier implies the repository's
existing unit-viscosity physical-tail evolution proposition. -/
theorem h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_all_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailPhysicalEvolutionOnRestartRadius
      (1 : ℝ)
      E
      (one_pos : (0 : ℝ) < 1)
      u
      T
      t
      hNS
      ht
      hE
      hTail := by
  intro q hqPos hEnd

  obtain ⟨hEndpoint, hAll⟩ :=
    hProduct q hqPos hEnd

  exact
    h3PreterminalTailPhysicalEvolutionAt_of_endpoint_all_productIntegrable
      hNS
      ht
      hqPos
      hEnd
      hE
      hTail
      hEndpoint
      hAll

/-- Radius-wide product integrability therefore gives exact decoder agreement
between the canonical unit-viscosity selected restart and the old preterminal
branch throughout their genuine overlap. -/
theorem h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap_of_unitViscosity_all_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hProduct :
      H3PreterminalTailUnitViscosityProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
      (h3PreterminalTailCanonicalSelectedRestart
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail)
      u
      t
      T
      (h3FinHeatLerayRestartRadius (1 : ℝ) E) := by
  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u
        T
        t
        hNS
        ht
        hE
        hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_all_productIntegrable
      hNS ht hE hTail hProduct

  exact
    h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap
      (one_pos : (0 : ℝ) < 1)
      hNS
      ht
      hE
      hTail
      hEvolution

end

end Euclidean
end Bridge
end PrimeTensor
