import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Identification

/-!
# Classicalization: reduce temporal-admissibility saturation to generatorwise domination

`Density.Identification` removed the spatial-density obstruction completely.
The only remaining endpoint-specific closure statement is

    divergence-free weak-test closed span
      ≤
    admissible weak-test closed span.

The admissible generator set differs from the unrestricted divergence-free
generator set by exactly one predicate:

    H3PreterminalTailCanonicalWeakTemporalLocallyDominated.

Therefore the cleanest next frontier is generatorwise: prove that every compact
smooth divergence-free weak test satisfies that temporal local-domination
predicate for the fixed endpoint problem.

Under that hypothesis, the unrestricted and admissible generator sets are
literally equal.  Hence their algebraic spans and topological closures are
equal, the temporal-admissibility saturation theorem follows, and the physical
`L²` vector evolution identity follows immediately.

No local-domination estimate is proved here.  This file only removes all
remaining Hilbert-space closure bookkeeping from that analytic question.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityTemporalReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Exact generatorwise temporal frontier -/

/-- Every compact smooth divergence-free weak test satisfies the local temporal
domination condition required by the weak FTC, for this fixed endpoint problem. -/
def H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
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
        hNS ht hEnd hTail) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PreterminalTailCanonicalWeakTemporalLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint φ

/-! ## Generator sets coincide under generatorwise domination -/

/-- Once every divergence-free weak test satisfies temporal local domination,
the endpoint-admissible generator set is exactly the unrestricted
divergence-free weak-test generator set. -/
theorem h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_eq_divergenceFreeWeakTestPhysicalL2Set_of_all_temporallyLocallyDominated
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set
        hNS ht htau hEnd hE hTail hEndpoint
      =
    h3DivergenceFreeWeakTestPhysicalL2Set := by
  apply Set.Subset.antisymm

  · exact
      h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_subset_divergenceFreeWeakTestPhysicalL2Set
        hNS ht htau hEnd hE hTail hEndpoint

  · intro Φ hΦ

    rcases hΦ with ⟨φ, hDiv, hEq⟩

    exact
      ⟨
        φ,
        hDiv,
        hAll φ hDiv,
        hEq
      ⟩

/-! ## Algebraic and closed spans coincide -/

/-- The algebraic admissible weak-test span equals the unrestricted
divergence-free weak-test span under generatorwise temporal domination. -/
theorem h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span_eq_divergenceFreeWeakTestPhysicalL2Span_of_all_temporallyLocallyDominated
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span
        hNS ht htau hEnd hE hTail hEndpoint
      =
    h3DivergenceFreeWeakTestPhysicalL2Span := by
  unfold
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span
    h3DivergenceFreeWeakTestPhysicalL2Span

  rw [
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Set_eq_divergenceFreeWeakTestPhysicalL2Set_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll
  ]

/-- The closed admissible weak-test span equals the unrestricted divergence-free
weak-test closed span under generatorwise temporal domination. -/
theorem h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan_eq_divergenceFreeWeakTestPhysicalL2ClosedSpan_of_all_temporallyLocallyDominated
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan
        hNS ht htau hEnd hE hTail hEndpoint
      =
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan := by
  unfold
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan

  rw [
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2Span_eq_divergenceFreeWeakTestPhysicalL2Span_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll
  ]

/-! ## Close temporal-admissibility saturation from the generator frontier -/

/-- Generatorwise temporal local domination implies the exact remaining
closed-span temporal-admissibility frontier. -/
theorem H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan_of_all_temporallyLocallyDominated
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan
      hNS ht htau hEnd hE hTail hEndpoint := by
  unfold
    H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan

  rw [
    h3PreterminalTailCanonicalAdmissibleWeakTestPhysicalL2ClosedSpan_eq_divergenceFreeWeakTestPhysicalL2ClosedSpan_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll
  ]

/-! ## Evolution identity from the sole analytic frontier -/

/-- Once every compact smooth divergence-free weak test satisfies the isolated
temporal local-domination condition, the physical `L²` vector evolution
identity follows. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_all_divergenceFreeWeakTests_temporallyLocallyDominated
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
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
        hNS ht htau hEnd hTail
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
      hNS ht htau hEnd hE hTail hEndpoint := by
  apply
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert_eq_BochnerProjectedRHS_of_temporalAdmissibility
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    H3PreterminalTailCanonicalDivergenceFreeWeakTestClosedSpanContainedInAdmissibleWeakTestClosedSpan_of_all_temporallyLocallyDominated
      hNS ht htau hEnd hE hTail hEndpoint hAll

end

end Euclidean
end Bridge
end PrimeTensor
