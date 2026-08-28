import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterFrequencySplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedConvolutionSecond

/-!
# Nine-quarter raw Fourier moment of the selected nonlinear convolution

The selected positive-time mild state now has an integrable `9/4` moment in the
canonical raw Fourier representative used by `h3RawProductConvolution`.

`NineQuarterFrequencySplit` closes the only new frequency algebra:

    w(ξ)
      ≤
    C₉ (w(η) + w(ξ - η)),

where

    w(ξ) = ‖ξ‖^(9/4)
    C₉   = 2^(9/4).

This file feeds that split into the same Young-convolution architecture already
used for the second Fourier moment.

For arbitrary H³ spectral scalar states `F`, `G`, assuming `9/4` moments on
both canonical raw representatives gives the majorant

    w(ξ) |(f̂ * ĝ)(ξ)|
      ≤
    C₉ ((w |f̂|) * |ĝ|)(ξ)
      +
    C₉ (|f̂| * (w |ĝ|))(ξ).

Both scalar convolutions are `L¹`, hence the exact raw product convolution has
an integrable `9/4` Fourier moment.

The final theorem specializes this propagation step to every pair of velocity
coordinates of the selected positive-time mild solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedRawConvolutionNineQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left `9/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionNineQuarterMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (h3FourierNineQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right `9/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionNineQuarterMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (h3FourierNineQuarterWeight (ξ - η) *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete `9/4`-moment Young majorant. -/
noncomputable def h3RawProductConvolutionNineQuarterMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierNineQuarterSplitCoefficient *
    (h3RawProductConvolutionNineQuarterMomentLeftMajorant F G ξ +
      h3RawProductConvolutionNineQuarterMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable `9/4` raw Fourier moment. -/
theorem h3RawProductConvolutionNineQuarterMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineQuarterMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hFq.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (h3FourierNineQuarterWeight η *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable `9/4` raw Fourier moment. -/
theorem h3RawProductConvolutionNineQuarterMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineQuarterMomentRightMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hF0 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hConv :=
    hF0.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hGq

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (h3FourierNineQuarterWeight (ξ - η) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar `9/4` convolution majorant is integrable. -/
theorem h3RawProductConvolutionNineQuarterMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineQuarterMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionNineQuarterMomentMajorant
  exact
    ((h3RawProductConvolutionNineQuarterMomentLeftMajorant_integrable
        F G hFq).add
      (h3RawProductConvolutionNineQuarterMomentRightMajorant_integrable
        F G hGq)).const_mul
          h3FourierNineQuarterSplitCoefficient

/-- The exact raw product convolution inherits an integrable `9/4` Fourier
moment from `9/4` moments on both input raw representatives. -/
theorem h3RawProductConvolution_nineQuarterMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let fq : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let gq : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierNineQuarterWeight ζ *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable f0 (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hG0 :
      Integrable g0 (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hLeftProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          fq p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hFq.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      fq, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * gq (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hGq
    simpa only [
      f0, gq,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            fq η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * gq (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  have hMajor :=
    h3RawProductConvolutionNineQuarterMomentMajorant_integrable
      F G hFq hGq

  have hWeightContinuous :
      Continuous h3FourierNineQuarterWeight := by
    unfold h3FourierNineQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    positivity

  have hCoeff0 :
      0 ≤ h3FourierNineQuarterSplitCoefficient := by
    unfold h3FourierNineQuarterSplitCoefficient
    exact Real.rpow_nonneg (by norm_num) _

  have hRawKernel :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η))
        (volume : Measure H3FourierPoint3) :=
    h3RawProductKernel_integrable F G ξ

  have hRawWeighted :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul
      (h3FourierNineQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterSplitCoefficient *
            (fq η * g0 (ξ - η) +
              f0 η * gq (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierNineQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierNineQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierNineQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
              rw [norm_mul]
      _ ≤
        (h3FourierNineQuarterSplitCoefficient *
          (h3FourierNineQuarterWeight η +
            h3FourierNineQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
        dsimp only [f0, g0, fq, gq]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
    exact integral_mono hRawWeighted hInnerMajor hPointwise

  have hNormIntegral :
      ‖h3RawProductConvolution F G ξ‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖ := by
    change
      ‖∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖
    exact norm_integral_le_integral_norm _

  have hBound :
      h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionNineQuarterMomentMajorant F G ξ := by
    calc
      h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖
          ≤
        h3FourierNineQuarterWeight ξ *
          (∫ η : H3FourierPoint3,
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_left hNormIntegral hw
      _ =
        ∫ η : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖ := by
        rw [integral_const_mul]
      _ ≤
        ∫ η : H3FourierPoint3,
          h3FourierNineQuarterSplitCoefficient *
            (fq η * g0 (ξ - η) +
              f0 η * gq (ξ - η)) :=
        hIntegralLe
      _ =
        h3RawProductConvolutionNineQuarterMomentMajorant F G ξ := by
        unfold h3RawProductConvolutionNineQuarterMomentMajorant
        unfold h3RawProductConvolutionNineQuarterMomentLeftMajorant
        unfold h3RawProductConvolutionNineQuarterMomentRightMajorant
        dsimp only [f0, g0, fq, gq]
        rw [← integral_add hLeftξ hRightξ]
        rw [← integral_const_mul]

  have hTargetNonneg :
      0 ≤
        h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hLeftNonneg :
      0 ≤
        h3RawProductConvolutionNineQuarterMomentLeftMajorant F G ξ := by
    unfold h3RawProductConvolutionNineQuarterMomentLeftMajorant
    exact integral_nonneg fun η => by
      have hwη : 0 ≤ h3FourierNineQuarterWeight η := by
        unfold h3FourierNineQuarterWeight
        positivity
      exact
        mul_nonneg
          (mul_nonneg hwη (norm_nonneg _))
          (norm_nonneg _)

  have hRightNonneg :
      0 ≤
        h3RawProductConvolutionNineQuarterMomentRightMajorant F G ξ := by
    unfold h3RawProductConvolutionNineQuarterMomentRightMajorant
    exact integral_nonneg fun η => by
      have hwShift :
          0 ≤ h3FourierNineQuarterWeight (ξ - η) := by
        unfold h3FourierNineQuarterWeight
        positivity
      exact
        mul_nonneg
          (norm_nonneg _)
          (mul_nonneg hwShift (norm_nonneg _))

  have hMajorNonneg :
      0 ≤
        h3RawProductConvolutionNineQuarterMomentMajorant F G ξ := by
    unfold h3RawProductConvolutionNineQuarterMomentMajorant
    positivity

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Selected positive-time specialization: every pair of velocity coordinates
has an exact raw product convolution with an integrable `9/4` Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_nineQuarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply h3RawProductConvolution_nineQuarterMoment_integrable_of

  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR j

end
end Euclidean
end Bridge
end PrimeTensor
