import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.VariationOfConstants
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Interaction.Derivative.Endpoint

/-!
# Endpoint-closed quotient-safe variation of constants

`Interaction.Derivative.Endpoint` removes the artificial strict-final-time
restriction from the interaction derivative:

    0 < s < q ≤ tau.

The remaining FTC and variation-of-constants argument already uses only:

* strong continuity of the interaction path on `[0,q]`;
* interval integrability of the retarded forcing kernel; and
* positivity of `q`.

Those facts are independent of whether `q < tau` or `q = tau`.

This file therefore carries the endpoint-closed derivative through the existing
FTC and quotient-safe variation-of-constants algebra.  The established
strict-interior theorems remain unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2VariationOfConstantsEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Endpoint-closed version of the negative-retarded-forcing interaction
derivative: the final target may equal `tau`. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_neg_retardedForcing_of_integralEvolution_to
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioc (0 : ℝ) tau)
    (hs : s ∈ Set.Ioo (0 : ℝ) q) :
    HasDerivWithinAt
      (h3PreterminalTailCanonicalRawFourierL2InteractionReal
        hNS ht htau.le hEnd hE hTail hEndpoint q)
      (- h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
        hNS ht htau.le hEnd hE hTail hEndpoint q s)
      (Set.Ioi s)
      s := by
  have hDerivative :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_of_integralEvolution_to
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq hs

  simpa only [
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal,
    h3RawFourierL2HeatApplyNN_neg
  ] using hDerivative

/-- Endpoint-closed FTC for the quotient-safe interaction picture. -/
theorem h3PreterminalTailCanonicalRawFourierL2InteractionReal_sub_eq_neg_retardedForcingIntegral_of_integralEvolution_to
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
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q q
        -
      h3PreterminalTailCanonicalRawFourierL2InteractionReal
          hNS ht htau.le hEnd hE hTail hEndpoint q 0
      =
    -
      ∫ s in (0 : ℝ)..q,
        h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
          hNS ht htau.le hEnd hE hTail hEndpoint q s := by
  let I : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal
      hNS ht htau.le hEnd hE hTail hEndpoint q

  let R : ℝ → H3RawFourierL2FinVectorState :=
    h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
      hNS ht htau.le hEnd hE hTail hEndpoint q

  have hIContinuous :
      ContinuousOn I (Set.Icc (0 : ℝ) q) :=
    (continuous_h3PreterminalTailCanonicalRawFourierL2InteractionReal
      hNS ht htau.le hEnd hE hTail hEndpoint).continuousOn

  have hRight :
      ∀ s ∈ Set.Ioo (0 : ℝ) q,
        HasDerivWithinAt
          I
          (-R s)
          (Set.Ioi s)
          s := by
    intro s hs
    dsimp only [I, R]
    exact
      h3PreterminalTailCanonicalRawFourierL2InteractionReal_hasDerivWithinAt_right_neg_retardedForcing_of_integralEvolution_to
        hNS ht htau hEnd hE hTail hEndpoint hEvolution hq hs

  have hIntegrable :
      IntervalIntegrable
        (fun s : ℝ => -R s)
        volume
        0
        q := by
    have hR :=
      h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal_intervalIntegrable
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q)
    dsimp only [R]
    exact hR.neg

  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hq.1.le
      hIContinuous
      hRight
      hIntegrable

  dsimp only [I, R] at hFTC
  rw [intervalIntegral.integral_neg] at hFTC

  exact hFTC.symm

/-- Endpoint-closed quotient-safe raw Fourier `L²` variation-of-constants
formula.  The final target may equal the ambient elapsed endpoint `tau`. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_of_integralEvolution_to
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
    (hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint)
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
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
  have hFTC :=
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_sub_eq_neg_retardedForcingIntegral_of_integralEvolution_to
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

  rw [
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_final
      hNS ht htau.le hEnd hE hTail hEndpoint,
    h3PreterminalTailCanonicalRawFourierL2InteractionReal_zero
      hNS ht htau hEnd hE hTail hEndpoint
  ] at hFTC

  calc
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
        +
      (h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint q
        -
       h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal q)
          (h3SpectralFinVectorRawFourierL2
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1))) := by
            abel
    _ =
      h3RawFourierL2HeatApplyNN
          1 zero_le_one
          (Real.toNNReal q)
          (h3SpectralFinVectorRawFourierL2
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1))
        +
      (-
        ∫ s in (0 : ℝ)..q,
          h3PreterminalTailCanonicalRawFourierL2RetardedForcingReal
            hNS ht htau.le hEnd hE hTail hEndpoint q s) := by
              rw [hFTC]
    _ =
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
            abel

end

end Euclidean
end Bridge
end PrimeTensor
