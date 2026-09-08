import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.Family

/-!
# Transport the vorticity closure to the raw Fourier L² evolution family

The vorticity route now supplies the genuine physical `L²` endpoint evolution
identity at every shortened elapsed target.

`Temporal.Endpoint.Fourier.L2.Evolution.Family` already proves the exact
Plancherel/Bochner transport from one such physical identity to the raw Fourier
integral equation required by the variation-of-constants branch.

This file performs that transport pointwise in the shortened target and exports
the full raw-Fourier evolution-family proposition directly from the endpoint H³
hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The endpoint H³ hypotheses imply the complete raw-Fourier `L²` integral
evolution family needed by the interaction/variation-of-constants branch. -/
theorem H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_endpointH3
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
    H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro q hq

  let qI : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq⟩

  have hPhysical :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail qI
        =
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
        hNS ht htau hEnd hE hTail hEndpoint qI :=
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_endpointH3
      hNS ht htau hEnd hE hTail hEndpoint qI

  dsimp only [qI] at hPhysical

  exact
    h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_intervalIntegral_spectralRHS_to_of_physicalL2Evolution
      hNS ht htau hEnd hE hTail hEndpoint
      ⟨q, hq⟩
      hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
