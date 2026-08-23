import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionPointwise

/-!
# Pointwise Young domination of the exact weighted H³ convolution

The previous file established the genuine scalar convolution kernel and the reflected
change of variables for the first Sobolev-weight term.  This file integrates the exact
pointwise weight-split estimate.

For weighted spectral states `F = W₃ f̂` and `G = W₃ ĝ`, we obtain

    ‖W₃(ξ) (f̂ * ĝ)(ξ)‖
      ≤ 8 * (
          ∫ η, ‖ĝ(η)‖ ‖F(ξ - η)‖
          +
          ∫ η, ‖f̂(η)‖ ‖G(ξ - η)‖).

Both scalar majorants are genuine `L¹` functions by Hölder (`L² * L² → L¹`).
The first is put into the endpoint-Young `L¹ * L²` orientation by the exact
reflection `η ↦ ξ - η` proved in `WeightedConvolutionPointwise`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionDomination
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The first scalar Sobolev-weight majorant is integrable for every output frequency. -/
theorem h3FirstYoungMajorant_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        ‖F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3) := by
  rw [← memLp_one_iff_integrable]
  exact
    (h3SpectralScalarRawFourier_reflectedShift_memLp2 G ξ).norm.mul'
      (r := (1 : ENNReal))
      (MeasureTheory.Lp.memLp F).norm

/-- The second scalar Sobolev-weight majorant is integrable for every output frequency. -/
theorem h3SecondYoungMajorant_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        ‖h3SpectralScalarRawFourier F η‖ *
          ‖G (ξ - η)‖)
      (volume : Measure H3FourierPoint3) := by
  rw [← memLp_one_iff_integrable]
  exact
    (h3SpectralScalarState_reflectedShift_memLp2 G ξ).norm.mul'
      (r := (1 : ENNReal))
      (h3SpectralScalarRawFourier_memLp2 F).norm

/-- The complete pointwise Sobolev-weight majorant is integrable. -/
theorem h3WeightedYoungMajorant_integrable
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    Integrable
      (fun η : H3FourierPoint3 =>
        8 *
          (‖F η‖ *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖
            +
           ‖h3SpectralScalarRawFourier F η‖ *
              ‖G (ξ - η)‖))
      (volume : Measure H3FourierPoint3) := by
  exact
    ((h3FirstYoungMajorant_integrable F G ξ).add
      (h3SecondYoungMajorant_integrable F G ξ)).const_mul (8 : ℝ)

/--
Exact pointwise weighted convolution domination by the two endpoint-Young majorants.
The first term has already been reflected so that the raw Fourier amplitude occupies the
`L¹` integration slot and the weighted state occupies the translated `L²` slot.
-/
theorem norm_h3WeightedRawProductConvolution_le_youngMajorants
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3WeightedRawProductConvolution F G ξ‖
      ≤
    8 *
      ((∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G η‖ *
            ‖F (ξ - η)‖)
        +
       ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖G (ξ - η)‖) := by
  rw [h3WeightedRawProductConvolution_eq_integral]

  have hFirst := h3FirstYoungMajorant_integrable F G ξ
  have hSecond := h3SecondYoungMajorant_integrable F G ξ
  have hDom := h3WeightedYoungMajorant_integrable F G ξ

  calc
    ‖∫ η : H3FourierPoint3,
        h3WeightedRawProductKernelAt F G η ξ‖
        ≤
      ∫ η : H3FourierPoint3,
        8 *
          (‖F η‖ *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖
            +
           ‖h3SpectralScalarRawFourier F η‖ *
              ‖G (ξ - η)‖) := by
      exact
        norm_integral_le_of_norm_le hDom <|
          Filter.Eventually.of_forall fun η =>
            norm_h3WeightedRawProductKernelAt_le F G η ξ
    _ =
      8 *
        ((∫ η : H3FourierPoint3,
            ‖h3SpectralScalarRawFourier G η‖ *
              ‖F (ξ - η)‖)
          +
         ∫ η : H3FourierPoint3,
            ‖h3SpectralScalarRawFourier F η‖ *
              ‖G (ξ - η)‖) := by
      rw [integral_const_mul]
      rw [integral_add hFirst hSecond]
      rw [h3FirstYoungMajorant_swap F G ξ]

end

end Euclidean
end Bridge
end PrimeTensor
