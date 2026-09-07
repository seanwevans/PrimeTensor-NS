import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Evolution.Family.Product
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification.Product.State

/-!
# Endpoint-closed product-integrable spectral Duhamel identity

The product-integrability frontier already yields the complete raw Fourier `L²`
integral evolution family on `[0,tau]`.

`Duhamel.Identification.Endpoint` now accepts every positive final target
`q ≤ tau`.

This file composes those two results and then lifts the endpoint-safe quotient
identity back to the actual weighted H³ spectral state using the existing exact
deweighting injectivity argument.

Thus the product-integrability route is valid at `q = tau` as well as every
strict interior positive target.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Interval

noncomputable section

/-- Under the all-tests product-integrability frontier, endpoint-safe raw
Fourier `L²` variation of constants lands on the actual spectral Duhamel state
for every `q ∈ (0,tau]`. -/
theorem h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_all_productIntegrable_to
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
    H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_of_all_productIntegrable
      hNS ht htau hEnd hE hTail hEndpoint hAll

  exact
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_integralEvolution_to
      hNS ht htau hEnd hE hTail hEndpoint hEvolution hq

/-- Under the all-tests product-integrability frontier, the normalized endpoint
canonical path satisfies the actual weighted H³ variation-of-constants identity
for every `q ∈ (0,tau]`. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_variationOfConstants_of_all_productIntegrable_to
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
    h3PreterminalTailCanonicalRawFourierL2VariationOfConstants_eq_spectralDuhamel_of_all_productIntegrable_to
      hNS ht htau hEnd hE hTail hEndpoint hAll hq

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
