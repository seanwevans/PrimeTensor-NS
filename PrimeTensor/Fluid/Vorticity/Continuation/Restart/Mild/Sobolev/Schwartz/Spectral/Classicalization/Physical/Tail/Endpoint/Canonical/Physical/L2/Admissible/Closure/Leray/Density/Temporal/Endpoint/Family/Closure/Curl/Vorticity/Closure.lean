import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Integrated

/-!
# Close endpoint physical L² evolution through the vorticity route

The preceding file proves the three integrated curl-test weak velocity
identities directly from the endpoint H³ hypotheses.

`Closure.Curl.Integrated` already packages the remaining Helmholtz step:

* those three integrated curl-test identities make every shortened physical
  evolution defect weakly curl-free;
* the defect is already Leray-fixed;
* Leray-fixed plus weakly curl-free forces the defect to vanish.

This file feeds the completed vorticity route into those generic closure
theorems and exports the resulting physical `L²` evolution identity with no
additional analytic hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Under the endpoint H³ hypotheses, every shortened physical evolution defect
is weakly curl-free. -/
theorem H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed_endpointH3
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
    H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hCurlIntegrated :
      H3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint :=
    h3PreterminalTailCanonicalCurlWeakVelocityPairingsSatisfyIntegratedProjectedRHSOnElapsed_endpointH3
      hNS ht htau hEnd hE hTail hEndpoint

  intro q

  exact
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_weakCurlFree_of_integratedCurlPairings
      hNS ht htau hEnd hE hTail hEndpoint
      hCurlIntegrated q

/-- Hence every shortened endpoint velocity increment is exactly the Bochner
integral of the projected physical `L²` RHS. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_endpointH3
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  have hCurl :
      H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint :=
    H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed_endpointH3
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_defects_weakCurlFree
      hNS ht htau hEnd hE hTail hEndpoint
      hCurl q

end

end Euclidean
end Bridge
end PrimeTensor
