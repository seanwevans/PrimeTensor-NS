import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.Family
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.WeakDerivative

/-!
# Raw Fourier L² endpoint evolution family from scalar weak derivatives

`Family.Closure.WeakDerivative` supplies the genuine physical `L²` evolution
identity at every shortened target `q ∈ [0,tau]` under the scalar weak-pairing
derivative frontier.

The transport theorem in `Fourier.L2.Evolution.Family` is independent of how
that physical identity was obtained.  Hence the raw-Fourier integral evolution
family follows without any coordinatewise spacetime product-integrability or
Fubini hypothesis.

No new Fourier or Bochner analysis is performed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The exact raw-Fourier evolution-family hypothesis required by the
interaction/variation-of-constants branch follows from the all-tests scalar
weak-pairing derivative frontier. -/
theorem H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_of_all_weakPairingDerivatives
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
      H3PreterminalTailCanonicalAllDivergenceFreeWeakVelocityPairingsHaveProjectedRHSDerivativeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint) :
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
        hNS ht htau hEnd hE hTail hEndpoint qI := by
    exact
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_weakPairingDerivatives
        hNS ht htau hEnd hE hTail hEndpoint hAll qI

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
