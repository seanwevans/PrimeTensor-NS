import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Third.Convolution.Majorant.Mass

/-!
# Fifth Fréchet endpoint: quantitative cubic mass of the exact raw convolution

`ThirdConvolutionMajorantMass` computes the exact total mass of the cubic Young
majorant.  This file exposes the corresponding pointwise domination of the
actual raw product convolution:

    |ξ|³ |(F̂ * Ĝ)(ξ)|
      ≤
    M₃(F,G)(ξ)

for almost every frequency.

Integrating that domination gives the numerical cubic convolution estimate

    m₃(F * G)
      ≤
    4 (m₃(F)m₀(G) + m₀(F)m₃(G)).

This is the quantitative convolution input needed to propagate the newly
closed selected-state cubic moment through the Leray-divergence forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointThirdConvolutionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution cubic weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionThirdMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 3 *
      ‖h3RawProductConvolution F G ξ‖

/-- The exact raw product convolution inherits an integrable cubic Fourier
moment from cubic moments on both input raw representatives. -/
theorem h3RawProductConvolution_thirdMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f3 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 3 *
        ‖h3SpectralScalarRawFourier F η‖

  let g3 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 3 *
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
          f3 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF3.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f3, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g3 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG3
    simpa only [
      f0, g3,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f3 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g3 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  have hMajor :=
    h3RawProductConvolutionThirdMomentMajorant_integrable
      F G hF3 hG3

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 3).aestronglyMeasurable).mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hCoeff0 :
      0 ≤ h3FourierThirdSplitCoefficient := by
    unfold h3FourierThirdSplitCoefficient
    norm_num

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
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (‖ξ‖ ^ 3)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierThirdSplitCoefficient *
            (f3 η * g0 (ξ - η) +
              f0 η * g3 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierThirdSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierThirdWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        ‖ξ‖ ^ 3 *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierThirdSplitCoefficient *
          (‖η‖ ^ 3 + ‖ξ - η‖ ^ 3)) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
        dsimp only [f0, g0, f3, g3]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
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
        ‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]

  calc
    ‖ξ‖ ^ 3 *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      ‖ξ‖ ^ 3 *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionThirdMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionThirdMomentMajorant
      unfold h3RawProductConvolutionThirdMomentLeftMajorant
      unfold h3RawProductConvolutionThirdMomentRightMajorant
      dsimp only [f0, g0, f3, g3]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw convolution is dominated almost everywhere by the cubic Young
majorant whose mass was computed in `ThirdConvolutionMajorantMass`. -/
theorem h3RawProductConvolution_thirdMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      ‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionThirdMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f3 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 3 *
        ‖h3SpectralScalarRawFourier F η‖

  let g3 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 3 *
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
          f3 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF3.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f3, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g3 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG3
    simpa only [
      f0, g3,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f3 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g3 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

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
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (‖ξ‖ ^ 3)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierThirdSplitCoefficient *
            (f3 η * g0 (ξ - η) +
              f0 η * g3 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierThirdSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierThirdWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        ‖ξ‖ ^ 3 *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierThirdSplitCoefficient *
          (‖η‖ ^ 3 + ‖ξ - η‖ ^ 3)) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
        dsimp only [f0, g0, f3, g3]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) := by
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
    ‖ξ‖ ^ 3 *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      ‖ξ‖ ^ 3 *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierThirdSplitCoefficient *
          (f3 η * g0 (ξ - η) +
            f0 η * g3 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionThirdMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionThirdMomentMajorant
      unfold h3RawProductConvolutionThirdMomentLeftMajorant
      unfold h3RawProductConvolutionThirdMomentRightMajorant
      dsimp only [f0, g0, f3, g3]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- Numerical cubic weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionThirdMass_le
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionThirdMass F G
      ≤
    h3FourierThirdSplitCoefficient *
      (h3SpectralScalarRawFourierThirdMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierThirdMass G) := by
  have hTarget :=
    h3RawProductConvolution_thirdMoment_integrable_of
      F G hF3 hG3

  have hMajor :=
    h3RawProductConvolutionThirdMomentMajorant_integrable
      F G hF3 hG3

  have hDom :=
    h3RawProductConvolution_thirdMoment_le_majorant_ae
      F G hF3 hG3

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionThirdMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionThirdMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionThirdMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierThirdSplitCoefficient *
        (h3SpectralScalarRawFourierThirdMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierThirdMass G) :=
      h3RawProductConvolutionThirdMomentMajorant_integral_eq
        F G hF3 hG3

end
end Euclidean
end Bridge
end PrimeTensor
