import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.FourierL2Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification.Endpoint

/-!
# Endpoint spectral Duhamel identity from the vorticity closure

The vorticity route now gives the complete raw-Fourier `L²` integral evolution
family directly from the endpoint H³ hypotheses.

The endpoint Duhamel-identification layer already converts that family into the
quotient-safe raw-Fourier variation-of-constants formula for every positive
`q ≤ tau`.

The same exact deweighting-injectivity argument used by the former
product-integrability route then lifts the raw identity back to the actual
weighted H³ spectral state.  No extra temporal product-integrability or weak
derivative hypothesis remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- Endpoint-safe raw-Fourier variation of constants from the endpoint H³
hypotheses alone. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_endpointH3_to
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
    h3PreterminalTailCanonicalSpectralDuhamelRawFourierL2Vector
      hNS ht htau.le hEnd hE hTail hEndpoint q := by
  have hEvolution :
      H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint :=
    H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_endpointH3
      hNS ht htau hEnd hE hTail hEndpoint

  exact
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_integralEvolution_to
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

/-- The normalized canonical endpoint path satisfies the actual weighted H³
variation-of-constants identity for every `q ∈ (0,tau]`, directly from the
endpoint H³ hypotheses. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_variationOfConstants_endpointH3_to
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
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint q
      =
    h3SpectralVelocityHeatApplyNN
        1 zero_le_one
        (Real.toNNReal q)
        (h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1)
      -
    h3SpectralFinHeatLerayDuhamel
      1 q one_pos
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint)
      (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau.le hEnd hE hTail hEndpoint) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let U0 : H3SpectralFinVectorState :=
    h3PreterminalCanonicalAnchorSpectralState
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1

  have hRaw :=
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_endpointH3_to
      hNS ht htau hEnd hE hTail hEndpoint hq

  change
    W q
      =
    h3SpectralVelocityHeatApplyNN
        1 zero_le_one (Real.toNNReal q) U0
      -
    h3SpectralFinHeatLerayDuhamel
      1 q one_pos W W

  funext i
  apply h3SpectralScalarRawFourierL2_injective

  have hRawI := congrFun hRaw i

  have hRawI' :
      h3SpectralScalarRawFourierL2 (W q i)
        =
      h3HeatFrequencyApplyNN
          1 zero_le_one (Real.toNNReal q)
          (h3SpectralScalarRawFourierL2 (U0 i))
        -
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i) := by
    change
      h3SpectralScalarRawFourierL2 (W q i)
        =
      h3HeatFrequencyApplyNN
          1 zero_le_one (Real.toNNReal q)
          (h3SpectralScalarRawFourierL2 (U0 i))
        -
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i)
      at hRawI
    exact hRawI

  change
    h3SpectralScalarRawFourierL2 (W q i)
      =
    h3SpectralScalarRawFourierL2
      (h3SpectralScalarHeatApplyNN
          1 zero_le_one (Real.toNNReal q) (U0 i)
        -
       h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i)

  calc
    h3SpectralScalarRawFourierL2 (W q i)
        =
      h3HeatFrequencyApplyNN
          1 zero_le_one (Real.toNNReal q)
          (h3SpectralScalarRawFourierL2 (U0 i))
        -
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i) :=
      hRawI'
    _ =
      h3SpectralScalarRawFourierL2
          (h3SpectralScalarHeatApplyNN
            1 zero_le_one (Real.toNNReal q) (U0 i))
        -
      h3SpectralScalarRawFourierL2
        (h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W i) := by
      rw [
        h3SpectralScalarRawFourierL2_heatApplyNN
          1 zero_le_one (Real.toNNReal q) (U0 i)
      ]
    _ =
      h3SpectralScalarRawFourierL2
        (h3SpectralScalarHeatApplyNN
            1 zero_le_one (Real.toNNReal q) (U0 i)
          -
         h3SpectralFinHeatLerayDuhamel
            1 q one_pos W W i) := by
      simpa only [h3SpectralScalarRawFourierL2CLM_apply] using
        (h3SpectralScalarRawFourierL2CLM.map_sub
          (h3SpectralScalarHeatApplyNN
            1 zero_le_one (Real.toNNReal q) (U0 i))
          (h3SpectralFinHeatLerayDuhamel
            1 q one_pos W W i)).symm

end

end Euclidean
end Bridge
end PrimeTensor
