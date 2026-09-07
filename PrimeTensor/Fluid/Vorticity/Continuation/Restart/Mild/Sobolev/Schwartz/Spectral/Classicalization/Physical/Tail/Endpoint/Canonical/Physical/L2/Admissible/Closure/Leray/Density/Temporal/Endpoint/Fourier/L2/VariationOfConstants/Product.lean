import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.VariationOfConstants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.Family.Product

/-!
# Raw Fourier L² endpoint variation of constants from product integrability

The quotient-safe variation-of-constants theorem is already proved under the
single abstract input

`H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed`.

`Evolution.Family.Product` now derives exactly that input from the endpoint
all-tests product-integrability frontier.  This file simply composes those two
results.

No interaction-picture, semigroup, generator, or Bochner argument is repeated.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- The quotient-safe raw Fourier `L²` variation-of-constants formula follows
from the endpoint all-tests product-integrability frontier. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_all_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
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
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyProductIntegrableOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioo (0 : ℝ) tau) :
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint q
      =
    h3RawFourierL2HeatApplyNN
        1 zero_le_one
        (Real.toNNReal q)
        (h3SpectralFinVectorRawFourierL2
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1))
      -
    ∫ s in (0 : ℝ)..q,
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s := by
  have hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint :=
    H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_of_all_productIntegrable
      hNS ht htau hEnd hE hTail hEndpoint hAll

  exact
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_integralEvolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

end

end Euclidean
end Bridge
end PrimeTensor
