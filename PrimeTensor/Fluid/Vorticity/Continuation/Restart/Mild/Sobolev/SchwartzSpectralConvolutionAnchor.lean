import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzProductConvolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralRawApproximation
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionDifference

/-!
# Exact Schwartz anchor for compact weighted H³ approximants

A smooth compact representative of a weighted H³ spectral state deweights to a
Schwartz function.  This file identifies the genuine PrimeTensor raw convolution
of two such weighted states with the ordinary Schwartz convolution of those
canonical deweighted representatives.

Taking inverse Fourier transforms of the deweighted Schwartz representatives then
turns the exact Schwartz product/convolution theorem into the physical product
anchor needed for the final density passage.  No limiting argument is used here;
`WeightedConvolutionDifference` supplies the quantitative continuity estimate for
that next rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal ContDiff FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralConvolutionAnchor
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw representative identification -/

/-- A smooth compact weighted representative deweights a.e. to the canonical
Schwartz representative. -/
theorem h3SpectralScalarRawFourier_ae_eq_deweightedSchwartz
    (F : H3SpectralScalarState)
    (g : H3FourierPoint3 → ℂ)
    (hF : (F : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hcompact : HasCompactSupport g)
    (hsmooth : ContDiff ℝ ∞ g) :
    h3SpectralScalarRawFourier F
      =ᵐ[volume]
    h3SmoothCompactDeweightedSchwartz g hcompact hsmooth := by
  filter_upwards [hF] with ξ hξ
  unfold h3SpectralScalarRawFourier
  rw [h3SmoothCompactDeweightedSchwartz_apply, hξ]

/-! ## Exact convolution anchor -/

/-- For two smooth compact weighted approximants, the genuine raw convolution is
exactly the Schwartz convolution of their canonical deweighted representatives. -/
theorem h3RawProductConvolution_eq_deweightedSchwartz_convolution
    (F G : H3SpectralScalarState)
    (f g : H3FourierPoint3 → ℂ)
    (hF : (F : H3FourierPoint3 → ℂ) =ᵐ[volume] f)
    (hG : (G : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hfcompact : HasCompactSupport f)
    (hgcompact : HasCompactSupport g)
    (hfsmooth : ContDiff ℝ ∞ f)
    (hgsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    h3RawProductConvolution F G ξ
      =
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth)
      (h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth) ξ := by
  let Sf : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth
  let Sg : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth

  have hRawF :
      h3SpectralScalarRawFourier F =ᵐ[volume] Sf := by
    simpa [Sf] using
      h3SpectralScalarRawFourier_ae_eq_deweightedSchwartz
        F f hF hfcompact hfsmooth

  have hRawG :
      h3SpectralScalarRawFourier G =ᵐ[volume] Sg := by
    simpa [Sg] using
      h3SpectralScalarRawFourier_ae_eq_deweightedSchwartz
        G g hG hgcompact hgsmooth

  have hShift :=
    hRawG.comp_tendsto
      (quasiMeasurePreserving_sub_left_of_right_invariant
        (volume : Measure H3FourierPoint3) ξ).tendsto_ae

  rw [SchwartzMap.convolution_apply]
  unfold MeasureTheory.convolution h3RawProductConvolution
  simp only [ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [hRawF, hShift] with η hηF hηG
  rw [hηF]
  simpa only [Function.comp_apply] using congrArg (fun z => Sf η * z) hηG

/-- Weighted form of the exact compact Schwartz convolution anchor. -/
theorem h3WeightedRawProductConvolution_eq_deweightedSchwartz_convolution
    (F G : H3SpectralScalarState)
    (f g : H3FourierPoint3 → ℂ)
    (hF : (F : H3FourierPoint3 → ℂ) =ᵐ[volume] f)
    (hG : (G : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hfcompact : HasCompactSupport f)
    (hgcompact : HasCompactSupport g)
    (hfsmooth : ContDiff ℝ ∞ f)
    (hgsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution F G ξ
      =
    (h3SobolevFrequencyWeight ξ : ℂ) *
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth)
        (h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth) ξ := by
  unfold h3WeightedRawProductConvolution
  rw [h3RawProductConvolution_eq_deweightedSchwartz_convolution
    F G f g hF hG hfcompact hgcompact hfsmooth hgsmooth ξ]

/-! ## Physical Schwartz product anchor -/

/-- The exact weighted convolution of two compact weighted approximants is the
weighted Fourier transform of the pointwise product of the inverse Fourier
transforms of their deweighted Schwartz representatives. -/
theorem h3WeightedRawProductConvolution_eq_weighted_fourier_product
    (F G : H3SpectralScalarState)
    (f g : H3FourierPoint3 → ℂ)
    (hF : (F : H3FourierPoint3 → ℂ) =ᵐ[volume] f)
    (hG : (G : H3FourierPoint3 → ℂ) =ᵐ[volume] g)
    (hfcompact : HasCompactSupport f)
    (hgcompact : HasCompactSupport g)
    (hfsmooth : ContDiff ℝ ∞ f)
    (hgsmooth : ContDiff ℝ ∞ g)
    (ξ : H3FourierPoint3) :
    h3WeightedRawProductConvolution F G ξ
      =
    (h3SobolevFrequencyWeight ξ : ℂ) *
      𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
          (𝓕⁻ (h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth))
          (𝓕⁻ (h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth))) ξ := by
  let Sf : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz f hfcompact hfsmooth
  let Sg : SchwartzMap H3FourierPoint3 ℂ :=
    h3SmoothCompactDeweightedSchwartz g hgcompact hgsmooth

  rw [h3WeightedRawProductConvolution_eq_deweightedSchwartz_convolution
    F G f g hF hG hfcompact hgcompact hfsmooth hgsmooth ξ]

  change
    (h3SobolevFrequencyWeight ξ : ℂ) *
        SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) Sf Sg ξ
      =
    (h3SobolevFrequencyWeight ξ : ℂ) *
      𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
          (𝓕⁻ Sf) (𝓕⁻ Sg)) ξ

  congr 1
  rw [h3Schwartz_fourier_product_apply_eq_convolution]
  rw [FourierTransform.fourier_fourierInv_eq,
      FourierTransform.fourier_fourierInv_eq]

end

end Euclidean
end Bridge
end PrimeTensor
