import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Closure

/-!
# Close endpoint physical L² evolution from weak curl-freeness of the defect

The temporal/Fubini branch proves the intermediate physical evolution defect

    D_q = (W(q) - W(0)) - ∫₀^q R(s) ds

vanishes by showing it annihilates every divergence-free compact weak test.

There is a second route already latent in the repository.

`Temporal.Endpoint.Family.Closure` proves unconditionally that every `D_q` lies
in the exact physical Leray-fixed submodule.  Separately, the completed
Fourier/Helmholtz density branch proves:

    Leray-fixed + weakly curl-free  ==>  zero

for arbitrary physical `L²` vectors.

Therefore the entire physical evolution identity follows if one can prove only
that `D_q` is weakly curl-free.  This is a natural target for the classical
preterminal vorticity equation: pressure disappears under curl before any
time/space Fubini step is attempted.

This file records that alternative closure.  No temporal product-integrability,
joint spacetime continuity, or scalar weak-FTC assumption is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Exact alternative temporal frontier: every shortened physical evolution
defect is weakly curl-free in the distributional `L²` sense. -/
def H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed
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
  ∀ q : Set.Icc (0 : ℝ) tau,
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree
      (h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q)

/-- A single shortened physical evolution defect vanishes as soon as it is
weakly curl-free.

The other half of the Helmholtz uniqueness pair, Leray-fixedness, is already
proved unconditionally by the endpoint family closure. -/
theorem h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_weakCurlFree
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
    (q : Set.Icc (0 : ℝ) tau)
    (hCurl :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree
        (h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
          hNS ht htau hEnd hE hTail hEndpoint q)) :
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q
      =
    0 := by
  have hFixed :
      h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
          hNS ht htau hEnd hE hTail hEndpoint q
        ∈
      h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_mem_lerayFixedSubmodule
      hNS ht htau hEnd hE hTail hEndpoint q

  exact
    H3PhysicalL2LerayFixedWeakCurlFreeTrivial_proved
      (h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo
        hNS ht htau hEnd hE hTail hEndpoint q)
      hFixed
      hCurl

/-- Weak curl-freeness of all shortened defects gives the genuine physical
`L²` evolution identity on every target `q ∈ [0,tau]`. -/
theorem h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_defects_weakCurlFree
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
    (hCurl :
      H3PreterminalTailCanonicalPhysicalL2EvolutionDefectsWeakCurlFreeOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
        hNS ht htau hEnd hTail q
      =
    h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
      hNS ht htau hEnd hE hTail hEndpoint q := by
  have hZero :=
    h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo_eq_zero_of_weakCurlFree
      hNS ht htau hEnd hE hTail hEndpoint q (hCurl q)

  unfold h3PreterminalTailCanonicalPhysicalL2EvolutionDefectTo at hZero

  exact sub_eq_zero.mp hZero

end

end Euclidean
end Bridge
end PrimeTensor
