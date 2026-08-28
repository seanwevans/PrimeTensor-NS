import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterConvolutionMajorantMass

/-!
# Sixth Fréchet endpoint: quantitative nineteen-quarter mass of the exact raw convolution

`NineteenQuarterConvolutionMajorantMass` computes the exact total mass of the
fractional Young majorant. This file proves the corresponding pointwise
domination of the actual complex raw product convolution:

    |ξ|^(19/4) |(F̂ * Ĝ)(ξ)|
      ≤
    M_{19/4}(F,G)(ξ)

for almost every frequency.

Integrating gives

    m_{19/4}(F * G)
      ≤
    2^(19/4)
      (m_{19/4}(F)m₀(G) + m₀(F)m_{19/4}(G)).

The final theorems specialize both inputs to coordinates of the selected mild
state using the newly closed selected `19/4` state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterConvolutionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution `19/4` weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionNineteenQuarterMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierNineteenQuarterWeight ξ *
      ‖h3RawProductConvolution F G ξ‖

/-- The exact raw product convolution inherits an integrable `19/4` Fourier
moment from `19/4` moments on both input raw representatives. -/
theorem h3RawProductConvolution_nineteenQuarterMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f19 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let g19 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierNineteenQuarterWeight ζ *
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
          f19 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF19.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f19, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g19 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG19
    simpa only [
      f0, g19,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f19 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g19 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  have hMajor :=
    h3RawProductConvolutionNineteenQuarterMomentMajorant_integrable
      F G hF19 hG19

  have hWeightContinuous :
      Continuous h3FourierNineteenQuarterWeight := by
    unfold h3FourierNineteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (19 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierNineteenQuarterWeight ξ := by
    unfold h3FourierNineteenQuarterWeight
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
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (h3FourierNineteenQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterSplitCoefficient *
            (f19 η * g0 (ξ - η) +
              f0 η * g19 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierNineteenQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierNineteenQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierNineteenQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierNineteenQuarterSplitCoefficient *
          (h3FourierNineteenQuarterWeight η +
            h3FourierNineteenQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) := by
        dsimp only [f0, g0, f19, g19]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) :=
    integral_mono hRawWeighted hInnerMajor hPointwise

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
        h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]

  calc
    h3FourierNineteenQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierNineteenQuarterWeight ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionNineteenQuarterMomentMajorant
      unfold h3RawProductConvolutionNineteenQuarterMomentLeftMajorant
      unfold h3RawProductConvolutionNineteenQuarterMomentRightMajorant
      dsimp only [f0, g0, f19, g19]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw convolution is dominated almost everywhere by the
`19/4` Young majorant whose mass was computed in the previous checkpoint. -/
theorem h3RawProductConvolution_nineteenQuarterMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f19 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let g19 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierNineteenQuarterWeight ζ *
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
          f19 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF19.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f19, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g19 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG19
    simpa only [
      f0, g19,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f19 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g19 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierNineteenQuarterWeight ξ := by
    unfold h3FourierNineteenQuarterWeight
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
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (h3FourierNineteenQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterSplitCoefficient *
            (f19 η * g0 (ξ - η) +
              f0 η * g19 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierNineteenQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierNineteenQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierNineteenQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierNineteenQuarterSplitCoefficient *
          (h3FourierNineteenQuarterWeight η +
            h3FourierNineteenQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) := by
        dsimp only [f0, g0, f19, g19]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) :=
    integral_mono hRawWeighted hInnerMajor hPointwise

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
    h3FourierNineteenQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierNineteenQuarterWeight ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineteenQuarterSplitCoefficient *
          (f19 η * g0 (ξ - η) +
            f0 η * g19 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionNineteenQuarterMomentMajorant
      unfold h3RawProductConvolutionNineteenQuarterMomentLeftMajorant
      unfold h3RawProductConvolutionNineteenQuarterMomentRightMajorant
      dsimp only [f0, g0, f19, g19]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- Numerical `19/4` weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionNineteenQuarterMass_le
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionNineteenQuarterMass F G
      ≤
    h3FourierNineteenQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierNineteenQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierNineteenQuarterMass G) := by
  have hTarget :=
    h3RawProductConvolution_nineteenQuarterMoment_integrable_of
      F G hF19 hG19

  have hMajor :=
    h3RawProductConvolutionNineteenQuarterMomentMajorant_integrable
      F G hF19 hG19

  have hDom :=
    h3RawProductConvolution_nineteenQuarterMoment_le_majorant_ae
      F G hF19 hG19

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionNineteenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierNineteenQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierNineteenQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierNineteenQuarterMass G) :=
      h3RawProductConvolutionNineteenQuarterMomentMajorant_integral_eq
        F G hF19 hG19

/-- Selected diagonal `19/4` raw-product-convolution envelope. -/
noncomputable def h3SelectedProductConvolutionNineteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3FourierNineteenQuarterSplitCoefficient *
    (h3SelectedMildNineteenQuarterMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A +
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildNineteenQuarterMomentEnvelope ν A t)

/-- Every selected positive-time scalar product convolution has an integrable
`19/4` raw Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_nineteenQuarterMoment_integrable
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
        h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  exact
    h3RawProductConvolution_nineteenQuarterMoment_integrable_of
      _
      _
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR j)

/-- Every selected positive-time scalar product convolution has its `19/4`
raw Fourier mass bounded by the explicit selected state envelope. -/
theorem h3RawProductConvolution_selectedRestart_nineteenQuarterMass_le
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
    h3RawProductConvolutionNineteenQuarterMass
        (W t i) (W t j)
      ≤
    h3SelectedProductConvolutionNineteenQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWi19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W t i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hWj19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR j

  have hBase :=
    h3RawProductConvolutionNineteenQuarterMass_le
      (W t i) (W t j) hWi19 hWj19

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

  have hWi19m :
      h3SpectralScalarRawFourierNineteenQuarterMass (W t i)
        ≤
      h3SelectedMildNineteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le
        hν U₀ hA hU₀ ht htR i

  have hWj19m :
      h3SpectralScalarRawFourierNineteenQuarterMass (W t j)
        ≤
      h3SelectedMildNineteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le
        hν U₀ hA hU₀ ht htR j

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM19nonneg :
      0 ≤ h3SelectedMildNineteenQuarterMomentEnvelope ν A t := by
    exact
      le_trans
        (h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W t i))
        hWi19m

  have hi0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t i)

  have hj0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t j)

  have hi19 :=
    h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W t i)

  have hj19 :=
    h3SpectralScalarRawFourierNineteenQuarterMass_nonneg (W t j)

  have hLeft :
      h3SpectralScalarRawFourierNineteenQuarterMass (W t i) *
          h3SpectralScalarRawFourierL1Mass (W t j)
        ≤
      h3SelectedMildNineteenQuarterMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul
      hWi19m
      hWj0
      hj0
      hM19nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W t i) *
          h3SpectralScalarRawFourierNineteenQuarterMass (W t j)
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildNineteenQuarterMomentEnvelope ν A t :=
    mul_le_mul
      hWi0
      hWj19m
      hj19
      hM0nonneg

  have hSum := add_le_add hLeft hRight

  have hCoeff0 :
      0 ≤ h3FourierNineteenQuarterSplitCoefficient :=
    h3FourierNineteenQuarterSplitCoefficient_nonneg

  unfold h3SelectedProductConvolutionNineteenQuarterMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum hCoeff0)

end
end Euclidean
end Bridge
end PrimeTensor
