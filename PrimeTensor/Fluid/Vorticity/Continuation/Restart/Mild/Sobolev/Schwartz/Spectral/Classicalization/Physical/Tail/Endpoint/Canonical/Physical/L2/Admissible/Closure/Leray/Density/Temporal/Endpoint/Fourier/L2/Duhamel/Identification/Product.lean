import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.VariationOfConstants.Product

/-!
# Endpoint spectral Duhamel identification from product integrability

`VariationOfConstants.Product` derives the quotient-safe raw Fourier `L²`
variation-of-constants formula from the endpoint all-tests product-integrability
frontier.

`Duhamel.Identification` already proves that the retarded Bochner integral in
that formula is exactly the raw-`L²` deweighting of the repository's spectral
heat--Leray Duhamel state.

This file composes those two facts.  No Duhamel, heat-semigroup, or Bochner
analysis is repeated.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- Under the endpoint all-tests product-integrability frontier, the quotient-
safe raw Fourier `L²` variation-of-constants formula lands exactly on the
repository's spectral heat--Leray Duhamel state. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_all_productIntegrable
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
    h3PreterminalTailCanonicalSpectralDuhamelRawFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint q := by
  have hVOC :=
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_all_productIntegrable
      hNS ht htau hEnd hE hTail hEndpoint hAll hq

  have hDuhamel :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_integral_eq_spectralDuhamelRawFourierL2Vector
      hNS ht htau hEnd hE hTail hEndpoint hq

  rw [hDuhamel] at hVOC
  exact hVOC

end

end Euclidean
end Bridge
end PrimeTensor
