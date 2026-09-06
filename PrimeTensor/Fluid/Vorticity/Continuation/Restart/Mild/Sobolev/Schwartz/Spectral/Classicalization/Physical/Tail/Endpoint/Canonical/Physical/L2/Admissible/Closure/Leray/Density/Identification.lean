import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Reduction

/-!
# Classicalization: identify the physical Leray subspace with weak-test closure

`Density.Closure` proved the difficult inclusion

    physical Leray-fixed L²
      ≤
    closure(span(divergence-free compact weak tests)).

`Density.Test.Fixed` had already proved the reverse inclusion.  Therefore the
two closed submodules are now exactly equal.

This turns the old endpoint-specific admissible-closure frontier into a purely
temporal statement.  The remaining condition

    Leray-fixed L² ≤ admissible weak-test closed span

is equivalent to

    unrestricted divergence-free weak-test closed span
      ≤
    admissible weak-test closed span.

In other words, after the completed spatial density theorem, the *only*
remaining endpoint obstruction is whether the temporal local-domination
restriction shrinks the closed test span.

No temporal domination theorem is asserted here.  This file only removes the
now-solved spatial density component from the endpoint frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityIdentification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact identification of the solenoidal physical L² subspace -/

/-- The closed span of compact smooth divergence-free weak tests is exactly
the physical Leray-fixed Hilbert submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule :
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
      =
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  exact
    (H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_iff_eq).1
      H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_proved

/-! ## The endpoint frontier is now exactly temporal admissibility -/

/-- With spatial Leray density proved, the previous endpoint-specific
Leray-subspace inclusion is equivalent to temporal-admissibility saturation of
the divergence-free weak-test closed span. -/
theorem h3PreterminalTailCanonicalPhysicalL2LerayFixedSubmoduleContainedInAdmissibleWeakTestClosedSpan_iff_temporalAdmissibility
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalPhysicalL2LerayFixedSubmoduleContainedInAdmissibleWeakTestClosedSpan
        hNS ht htau hEnd hE hTail hEndpoint
      ↔
    H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan
        hNS ht htau hEnd hE hTail hEndpoint := by
  unfold
    H3PreterminalTailCanonicalPhysicalL2LerayFixedSubmoduleContainedInAdmissibleWeakTestClosedSpan
    H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan

  rw [
    ← h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule
  ]

/-! ## Evolution identity reduced to the sole temporal frontier -/

/-- Temporal-admissibility saturation alone now implies membership of both
physical evolution terms in the admissible closed span. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionTermsInAdmissibleWeakTestClosedSpan_of_temporalAdmissibility
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hTemporal :
      H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalPhysicalL2EvolutionTermsInAdmissibleWeakTestClosedSpan
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalPhysicalL2EvolutionTermsInAdmissibleWeakTestClosedSpan_of_lerayFixedSubmoduleContained
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    (h3PreterminalTailCanonicalPhysicalL2LerayFixedSubmoduleContainedInAdmissibleWeakTestClosedSpan_iff_temporalAdmissibility
      hNS ht htau hEnd hE hTail hEndpoint).2
      hTemporal

/-- The physical vector evolution identity is now conditional only on the
endpoint-specific temporal-admissibility saturation statement. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_temporalAdmissibility
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hTemporal :
      H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_lerayFixedSubmoduleContained
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    (h3PreterminalTailCanonicalPhysicalL2LerayFixedSubmoduleContainedInAdmissibleWeakTestClosedSpan_iff_temporalAdmissibility
      hNS ht htau hEnd hE hTail hEndpoint).2
      hTemporal

end

end Euclidean
end Bridge
end PrimeTensor
