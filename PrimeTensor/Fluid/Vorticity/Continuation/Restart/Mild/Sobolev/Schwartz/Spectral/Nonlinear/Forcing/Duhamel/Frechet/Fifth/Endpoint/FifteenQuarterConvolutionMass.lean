import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterConvolutionMajorantMass

/-!
# Fifth Fréchet endpoint: quantitative fifteen-quarter mass of the exact raw convolution

`FifteenQuarterConvolutionMajorantMass` computes the exact total mass of the
fractional Young majorant.  This file exposes the corresponding pointwise
domination of the actual complex raw product convolution:

    |ξ|^(15/4) |(F̂ * Ĝ)(ξ)|
      ≤
    M_{15/4}(F,G)(ξ)

for almost every frequency.

Integrating gives

    m_{15/4}(F * G)
      ≤
    2^(15/4)
      (m_{15/4}(F)m₀(G) + m₀(F)m_{15/4}(G)).

The final theorem specializes both inputs to coordinates of the selected mild
state, using the newly closed selected `15/4` state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterConvolutionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution `15/4` weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionFifteenQuarterMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFifteenQuarterWeight ξ *
      ‖h3RawProductConvolution F G ξ‖

/-- The exact raw product convolution inherits an integrable `15/4` Fourier
moment from `15/4` moments on both input raw representatives. -/
theorem h3RawProductConvolution_fifteenQuarterMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f15 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierFifteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let g15 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierFifteenQuarterWeight ζ *
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
          f15 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF15.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f15, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g15 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG15
    simpa only [
      f0, g15,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f15 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g15 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  have hMajor :=
    h3RawProductConvolutionFifteenQuarterMomentMajorant_integrable
      F G hF15 hG15

  have hWeightContinuous :
      Continuous h3FourierFifteenQuarterWeight := by
    unfold h3FourierFifteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (15 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

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
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (h3FourierFifteenQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterSplitCoefficient *
            (f15 η * g0 (ξ - η) +
              f0 η * g15 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierFifteenQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierFifteenQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierFifteenQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierFifteenQuarterSplitCoefficient *
          (h3FourierFifteenQuarterWeight η +
            h3FourierFifteenQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
        dsimp only [f0, g0, f15, g15]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
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

  have hTargetNonneg :
      0 ≤
        h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]

  calc
    h3FourierFifteenQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierFifteenQuarterWeight ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionFifteenQuarterMomentMajorant
      unfold h3RawProductConvolutionFifteenQuarterMomentLeftMajorant
      unfold h3RawProductConvolutionFifteenQuarterMomentRightMajorant
      dsimp only [f0, g0, f15, g15]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw convolution is dominated almost everywhere by the
`15/4` Young majorant whose mass was computed in the previous checkpoint. -/
theorem h3RawProductConvolution_fifteenQuarterMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f15 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierFifteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let g15 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierFifteenQuarterWeight ζ *
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
          f15 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF15.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f15, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g15 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG15
    simpa only [
      f0, g15,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f15 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g15 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

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
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (h3FourierFifteenQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterSplitCoefficient *
            (f15 η * g0 (ξ - η) +
              f0 η * g15 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierFifteenQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierFifteenQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierFifteenQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierFifteenQuarterSplitCoefficient *
          (h3FourierFifteenQuarterWeight η +
            h3FourierFifteenQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
        dsimp only [f0, g0, f15, g15]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) := by
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

  calc
    h3FourierFifteenQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierFifteenQuarterWeight ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifteenQuarterSplitCoefficient *
          (f15 η * g0 (ξ - η) +
            f0 η * g15 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionFifteenQuarterMomentMajorant
      unfold h3RawProductConvolutionFifteenQuarterMomentLeftMajorant
      unfold h3RawProductConvolutionFifteenQuarterMomentRightMajorant
      dsimp only [f0, g0, f15, g15]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- Numerical `15/4` weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionFifteenQuarterMass_le
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionFifteenQuarterMass F G
      ≤
    h3FourierFifteenQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierFifteenQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFifteenQuarterMass G) := by
  have hTarget :=
    h3RawProductConvolution_fifteenQuarterMoment_integrable_of
      F G hF15 hG15

  have hMajor :=
    h3RawProductConvolutionFifteenQuarterMomentMajorant_integrable
      F G hF15 hG15

  have hDom :=
    h3RawProductConvolution_fifteenQuarterMoment_le_majorant_ae
      F G hF15 hG15

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionFifteenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierFifteenQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierFifteenQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFifteenQuarterMass G) :=
      h3RawProductConvolutionFifteenQuarterMomentMajorant_integral_eq
        F G hF15 hG15

/-- Selected diagonal `15/4` raw-product-convolution envelope. -/
noncomputable def h3SelectedProductConvolutionFifteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3FourierFifteenQuarterSplitCoefficient *
    (h3SelectedMildFifteenQuarterMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A +
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFifteenQuarterMomentEnvelope ν A t)

/-- Every selected positive-time scalar product convolution has an integrable
`15/4` raw Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_fifteenQuarterMoment_integrable
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
        h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  exact
    h3RawProductConvolution_fifteenQuarterMoment_integrable_of
      _
      _
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR j)

/-- Every selected positive-time scalar product convolution has its `15/4`
raw Fourier mass bounded by the explicit selected state envelope. -/
theorem h3RawProductConvolution_selectedRestart_fifteenQuarterMass_le
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
    h3RawProductConvolutionFifteenQuarterMass
        (W t i) (W t j)
      ≤
    h3SelectedProductConvolutionFifteenQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWi15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W t i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hWj15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR j

  have hBase :=
    h3RawProductConvolutionFifteenQuarterMass_le
      (W t i) (W t j) hWi15 hWj15

  have hWi0 :
      h3SpectralScalarRawFourierL1Mass (W t i)
        ≤
      h3SelectedRestartRawFourierL1Envelope A := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ t i

  have hWj0 :
      h3SpectralScalarRawFourierL1Mass (W t j)
        ≤
      h3SelectedRestartRawFourierL1Envelope A := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ t j

  have hWi15m :
      h3SpectralScalarRawFourierFifteenQuarterMass (W t i)
        ≤
      h3SelectedMildFifteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMass_le
        hν U₀ hA hU₀ ht htR i

  have hWj15m :
      h3SpectralScalarRawFourierFifteenQuarterMass (W t j)
        ≤
      h3SelectedMildFifteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMass_le
        hν U₀ hA hU₀ ht htR j

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM15nonneg :
      0 ≤ h3SelectedMildFifteenQuarterMomentEnvelope ν A t := by
    exact
      le_trans
        (h3SpectralScalarRawFourierFifteenQuarterMass_nonneg (W t i))
        hWi15m

  have hi0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t i)

  have hj0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t j)

  have hi15 :=
    h3SpectralScalarRawFourierFifteenQuarterMass_nonneg (W t i)

  have hj15 :=
    h3SpectralScalarRawFourierFifteenQuarterMass_nonneg (W t j)

  have hLeft :
      h3SpectralScalarRawFourierFifteenQuarterMass (W t i) *
          h3SpectralScalarRawFourierL1Mass (W t j)
        ≤
      h3SelectedMildFifteenQuarterMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul
      hWi15m
      hWj0
      hj0
      hM15nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W t i) *
          h3SpectralScalarRawFourierFifteenQuarterMass (W t j)
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFifteenQuarterMomentEnvelope ν A t :=
    mul_le_mul
      hWi0
      hWj15m
      hj15
      hM0nonneg

  have hSum := add_le_add hLeft hRight

  have hCoeff0 :
      0 ≤ h3FourierFifteenQuarterSplitCoefficient :=
    h3FourierFifteenQuarterSplitCoefficient_nonneg

  unfold h3SelectedProductConvolutionFifteenQuarterMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum hCoeff0)

end
end Euclidean
end Bridge
end PrimeTensor
