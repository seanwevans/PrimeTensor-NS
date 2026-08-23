import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionMajorantRepresentatives

/-!
# Global L² closure of the weighted H³ convolution

The two scalar endpoint-Young majorants have now been identified with genuine real `L²` states.
This file combines them into the full majorant

    M(F,G) = 8 (A(F,G) + B(F,G)),

proves the exact weighted Fourier convolution is strongly measurable, and transfers the pointwise
bound

    ‖W(ξ) (f̂ * ĝ)(ξ)‖ ≤ M(F,G)(ξ)

to a global `L²` estimate.  The final constant is

    16 * h3SobolevDeweightingConstant.

Thus the genuine weighted scalar product convolution itself defines an `H3SpectralScalarState`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter ContinuousLinearMap
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3WeightedConvolutionL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Bundled real `L²` state for the complete weighted Young majorant. -/
noncomputable def h3WeightedYoungMajorantL2
    (F G : H3SpectralScalarState) :
    H3FourierRealL2 :=
  (8 : ℝ) •
    (h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G)

/-- The bundled complete majorant has exactly the named scalar representative a.e. -/
theorem h3WeightedYoungMajorantL2_ae
    (F G : H3SpectralScalarState) :
    (h3WeightedYoungMajorantL2 F G : H3FourierPoint3 → ℝ)
      =ᵐ[volume]
    h3WeightedYoungMajorant F G := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (8 : ℝ)
      (h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G),
    MeasureTheory.Lp.coeFn_add
      (h3FirstYoungMajorantL2 F G)
      (h3SecondYoungMajorantL2 F G),
    h3FirstYoungMajorantL2_ae F G,
    h3SecondYoungMajorantL2_ae F G
  ] with ξ hSmul hAdd hFirst hSecond
  change
    ((8 : ℝ) •
      (h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G) :
        H3FourierRealL2) ξ
      = h3WeightedYoungMajorant F G ξ
  rw [hSmul]
  change
    8 *
      ((h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G :
        H3FourierRealL2) ξ)
      = h3WeightedYoungMajorant F G ξ
  rw [hAdd]
  simp only [Pi.add_apply]
  rw [hFirst, hSecond]
  rfl

/-- The full scalar Young majorant belongs to `L²`. -/
theorem h3WeightedYoungMajorant_memLp2
    (F G : H3SpectralScalarState) :
    MemLp
      (h3WeightedYoungMajorant F G)
      2
      (volume : Measure H3FourierPoint3) := by
  refine
    (MeasureTheory.Lp.memLp
      (h3WeightedYoungMajorantL2 F G)).congr_norm
      (h3WeightedYoungMajorant_aestronglyMeasurable F G)
      ?_
  filter_upwards [h3WeightedYoungMajorantL2_ae F G] with ξ hξ
  rw [hξ]

/-- Quantitative `L²` bound for the complete scalar Young majorant. -/
theorem norm_h3WeightedYoungMajorantL2_le
    (F G : H3SpectralScalarState) :
    ‖h3WeightedYoungMajorantL2 F G‖
      ≤ 16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
  have hSum :
      ‖h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G‖
        ≤
      h3SobolevDeweightingConstant * ‖G‖ * ‖F‖
        + h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
    exact
      (norm_add_le
        (h3FirstYoungMajorantL2 F G)
        (h3SecondYoungMajorantL2 F G)).trans
        (add_le_add
          (norm_h3FirstYoungMajorantL2_le F G)
          (norm_h3SecondYoungMajorantL2_le F G))

  calc
    ‖h3WeightedYoungMajorantL2 F G‖
        = 8 * ‖h3FirstYoungMajorantL2 F G + h3SecondYoungMajorantL2 F G‖ := by
            rw [h3WeightedYoungMajorantL2, norm_smul, Real.norm_eq_abs]
            norm_num
    _ ≤
      8 *
        (h3SobolevDeweightingConstant * ‖G‖ * ‖F‖
          + h3SobolevDeweightingConstant * ‖F‖ * ‖G‖) := by
            exact mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = 16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
            ring

/-- The genuine weighted product convolution belongs to Fourier `L²`. -/
theorem h3WeightedRawProductConvolution_memLp2
    (F G : H3SpectralScalarState) :
    MemLp
      (h3WeightedRawProductConvolution F G)
      2
      (volume : Measure H3FourierPoint3) := by
  refine
    (h3WeightedYoungMajorant_memLp2 F G).mono'
      ?_
      (Eventually.of_forall fun ξ =>
        norm_h3WeightedRawProductConvolution_le_majorant F G ξ)

  unfold h3WeightedRawProductConvolution
  apply AEStronglyMeasurable.mul
  · exact
      (Complex.continuous_ofReal.comp
        continuous_h3SobolevFrequencyWeight).aestronglyMeasurable
  · unfold h3RawProductConvolution

    have hF :=
      (h3SpectralScalarRawFourier_memLp2 F).1
    have hG :=
      (h3SpectralScalarRawFourier_memLp2 G).1

    have hJoint :=
      hF.convolution_integrand (mul ℂ ℂ) hG

    simpa only [mul_apply'] using
      hJoint.integral_prod_right'

/-- The genuine weighted scalar product convolution, bundled as an H³ spectral state. -/
noncomputable def h3WeightedRawProductConvolutionL2
    (F G : H3SpectralScalarState) :
    H3SpectralScalarState :=
  (h3WeightedRawProductConvolution_memLp2 F G).toLp
    (h3WeightedRawProductConvolution F G)

/-- The bundled genuine product has the exact weighted convolution representative a.e. -/
theorem h3WeightedRawProductConvolutionL2_ae
    (F G : H3SpectralScalarState) :
    (h3WeightedRawProductConvolutionL2 F G : H3FourierPoint3 → ℂ)
      =ᵐ[volume]
    h3WeightedRawProductConvolution F G := by
  exact MemLp.coeFn_toLp (h3WeightedRawProductConvolution_memLp2 F G)

/-- The genuine weighted convolution is norm-dominated by the bundled Young majorant. -/
theorem norm_h3WeightedRawProductConvolutionL2_le_majorant
    (F G : H3SpectralScalarState) :
    ‖h3WeightedRawProductConvolutionL2 F G‖
      ≤ ‖h3WeightedYoungMajorantL2 F G‖ := by
  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖(h3WeightedRawProductConvolutionL2 F G : H3FourierPoint3 → ℂ) ξ‖
          ≤
        ‖(h3WeightedYoungMajorantL2 F G : H3FourierPoint3 → ℝ) ξ‖ := by
    filter_upwards [
      h3WeightedRawProductConvolutionL2_ae F G,
      h3WeightedYoungMajorantL2_ae F G
    ] with ξ hProduct hMajorant
    rw [hProduct, hMajorant, Real.norm_eq_abs,
      abs_of_nonneg]
    · exact norm_h3WeightedRawProductConvolution_le_majorant F G ξ
    · unfold h3WeightedYoungMajorant
      exact
        mul_nonneg (by norm_num)
          (add_nonneg
            (h3FirstYoungMajorant_nonneg F G ξ)
            (h3SecondYoungMajorant_nonneg F G ξ))

  rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def]
  exact
    ENNReal.toReal_mono
      (MeasureTheory.Lp.eLpNorm_ne_top (h3WeightedYoungMajorantL2 F G))
      (eLpNorm_mono_ae hDom)

/-- Scalar H³ algebra estimate for the genuine weighted Fourier product convolution. -/
theorem norm_h3WeightedRawProductConvolutionL2_le
    (F G : H3SpectralScalarState) :
    ‖h3WeightedRawProductConvolutionL2 F G‖
      ≤ 16 * h3SobolevDeweightingConstant * ‖F‖ * ‖G‖ := by
  exact
    (norm_h3WeightedRawProductConvolutionL2_le_majorant F G).trans
      (norm_h3WeightedYoungMajorantL2_le F G)

end

end Euclidean
end Bridge
end PrimeTensor
