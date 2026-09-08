import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Mild.Vorticity

/-!
# Radius-wide physical tail evolution from endpoint continuity

The vorticity route has discharged the mild-equation half of the old physical
tail evolution frontier.

At one positive elapsed target, the only remaining input is now the reduced
endpoint physical `L²` continuity witness.  This file packages that single
hypothesis over the full canonical unit-viscosity restart radius and feeds it
through the existing overlap machinery.

No temporal product-integrability, weak-pairing derivative, overlap uniqueness,
decoder, or selected-restart argument is reproved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEvolutionVorticity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radius-wide unit-viscosity endpoint-continuity frontier.

For every positive elapsed target in the canonical restart radius, and every
proof that the old branch still exists through that target, it supplies exactly
the reduced endpoint physical `L²` continuity witness.  The vorticity closure
now supplies the mild equation automatically. -/
def H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
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
        H3PreterminalCanonicalL2EndpointContinuousOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide endpoint physical `L²` continuity implies the repository's
existing unit-viscosity physical-tail evolution proposition. -/
theorem h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
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

  have hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail :=
    hContinuity q hqPos hEnd

  exact
    h3PreterminalTailPhysicalEvolutionAt_of_endpointH3
      hNS
      ht
      hqPos
      hEnd
      hE
      hTail
      hEndpoint

/-- Radius-wide endpoint physical `L²` continuity therefore gives exact decoder
agreement between the canonical unit-viscosity selected restart and the old
preterminal branch throughout their genuine overlap. -/
theorem h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap_of_unitViscosity_endpointContinuity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hContinuity :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
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
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS ht hE hTail hContinuity

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
