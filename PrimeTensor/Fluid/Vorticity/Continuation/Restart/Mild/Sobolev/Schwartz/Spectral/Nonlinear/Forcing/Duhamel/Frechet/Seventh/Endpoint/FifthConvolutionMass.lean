import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Seventh.Endpoint.FifthConvolutionMajorantMass

/-!
# Seventh Fréchet endpoint: quantitative fifth mass of the exact raw convolution

`FifthConvolutionMajorantMass` computes the exact total mass of the scalar
fifth-moment Young majorant. This file exposes the corresponding pointwise
domination of the actual complex raw product convolution:

    |ξ|^5 |(F̂ * Ĝ)(ξ)|
      ≤
    M₅(F,G)(ξ)

for almost every frequency.

Integrating gives

    m₅(F * G)
      ≤
    2^5 (m₅(F)m₀(G) + m₀(F)m₅(G)).

The final theorem specializes both inputs to coordinates of the selected mild
state, using the newly closed canonical selected fifth-moment state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSeventhEndpointFifthConvolutionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution fifth weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionFifthMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 5 *
      ‖h3RawProductConvolution F G ξ‖

/-- The scalar fifth-moment convolution majorant is pointwise nonnegative. -/
theorem h3RawProductConvolutionFifthMomentMajorant_nonneg
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3RawProductConvolutionFifthMomentMajorant F G ξ := by
  have hLeft :
      0 ≤ h3RawProductConvolutionFifthMomentLeftMajorant F G ξ := by
    unfold h3RawProductConvolutionFifthMomentLeftMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (mul_nonneg
            (pow_nonneg (norm_nonneg η) 5)
            (norm_nonneg _))
          (norm_nonneg _)

  have hRight :
      0 ≤ h3RawProductConvolutionFifthMomentRightMajorant F G ξ := by
    unfold h3RawProductConvolutionFifthMomentRightMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (norm_nonneg _)
          (mul_nonneg
            (pow_nonneg (norm_nonneg (ξ - η)) 5)
            (norm_nonneg _))

  unfold h3RawProductConvolutionFifthMomentMajorant
  exact
    mul_nonneg
      h3FourierFifthSplitCoefficient_nonneg
      (add_nonneg hLeft hRight)

/-- The exact raw convolution is dominated almost everywhere by the fifth
Young majorant whose mass was computed in the previous checkpoint. -/
theorem h3RawProductConvolution_fifthMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionFifthMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f5 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 5 *
        ‖h3SpectralScalarRawFourier F η‖

  let g5 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 5 *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable f0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hG0 :
      Integrable g0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hLeftProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f5 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF5.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f5, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g5 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG5
    simpa only [
      f0, g5,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f5 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g5 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ ‖ξ‖ ^ 5 :=
    pow_nonneg (norm_nonneg ξ) 5

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
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (‖ξ‖ ^ 5)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifthSplitCoefficient *
            (f5 η * g0 (ξ - η) +
              f0 η * g5 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierFifthSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierFifthSplitCoefficient *
          (f5 η * g0 (ξ - η) +
            f0 η * g5 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierFifthWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      ‖ξ‖ ^ 5 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        ‖ξ‖ ^ 5 *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierFifthSplitCoefficient *
          (‖η‖ ^ 5 + ‖ξ - η‖ ^ 5)) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right
          hFreq hProdNonneg
      _ =
        h3FourierFifthSplitCoefficient *
          (f5 η * g0 (ξ - η) +
            f0 η * g5 (ξ - η)) := by
        dsimp only [f0, g0, f5, g5]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifthSplitCoefficient *
          (f5 η * g0 (ξ - η) +
            f0 η * g5 (ξ - η)) :=
    integral_mono
      hRawWeighted hInnerMajor hPointwise

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
    ‖ξ‖ ^ 5 *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      ‖ξ‖ ^ 5 *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left
        hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierFifthSplitCoefficient *
          (f5 η * g0 (ξ - η) +
            f0 η * g5 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionFifthMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionFifthMomentMajorant
      unfold h3RawProductConvolutionFifthMomentLeftMajorant
      unfold h3RawProductConvolutionFifthMomentRightMajorant
      dsimp only [f0, g0, f5, g5]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw product convolution inherits an integrable fifth Fourier
moment from fifth moments on both input raw representatives. -/
theorem h3RawProductConvolution_fifthMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMajor :=
    h3RawProductConvolutionFifthMomentMajorant_integrable
      F G hF5 hG5

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 5).aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  have hDom :=
    h3RawProductConvolution_fifthMoment_le_majorant_ae
      F G hF5 hG5

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hDom] with ξ hξ

  have hTarget0 :
      0 ≤
        ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 5)
      (norm_nonneg _)

  have hMajor0 :
      0 ≤
        h3RawProductConvolutionFifthMomentMajorant F G ξ :=
    h3RawProductConvolutionFifthMomentMajorant_nonneg
      F G ξ

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0,
    abs_of_nonneg hMajor0
  ] using hξ

/-- Numerical fifth weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionFifthMass_le
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionFifthMass F G
      ≤
    h3FourierFifthSplitCoefficient *
      (h3SpectralScalarRawFourierFifthMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFifthMass G) := by
  have hTarget :=
    h3RawProductConvolution_fifthMoment_integrable_of
      F G hF5 hG5

  have hMajor :=
    h3RawProductConvolutionFifthMomentMajorant_integrable
      F G hF5 hG5

  have hDom :=
    h3RawProductConvolution_fifthMoment_le_majorant_ae
      F G hF5 hG5

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifthMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionFifthMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifthMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierFifthSplitCoefficient *
        (h3SpectralScalarRawFourierFifthMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFifthMass G) :=
      h3RawProductConvolutionFifthMomentMajorant_integral_eq
        F G hF5 hG5

/-- Selected diagonal fifth raw-product-convolution envelope. -/
noncomputable def h3SelectedProductConvolutionFifthMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3FourierFifthSplitCoefficient *
    (h3SelectedMildFifthMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A +
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFifthMomentEnvelope ν A t)

/-- Every selected positive-time scalar product convolution has an integrable
fifth raw Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_fifthMoment_integrable
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
        ‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  exact
    h3RawProductConvolution_fifthMoment_integrable_of
      _
      _
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR j)

/-- Every selected positive-time scalar product convolution has its fifth raw
Fourier mass bounded by the explicit selected state envelope. -/
theorem h3RawProductConvolution_selectedRestart_fifthMass_le
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
    h3RawProductConvolutionFifthMass
        (W t i) (W t j)
      ≤
    h3SelectedProductConvolutionFifthMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWi5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier (W t i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hWj5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR j

  have hBase :=
    h3RawProductConvolutionFifthMass_le
      (W t i) (W t j) hWi5 hWj5

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

  have hWi5m :
      h3SpectralScalarRawFourierFifthMass (W t i)
        ≤
      h3SelectedMildFifthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMass_le
        hν U₀ hA hU₀ ht htR i

  have hWj5m :
      h3SpectralScalarRawFourierFifthMass (W t j)
        ≤
      h3SelectedMildFifthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifthMass_le
        hν U₀ hA hU₀ ht htR j

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM5nonneg :
      0 ≤ h3SelectedMildFifthMomentEnvelope ν A t := by
    exact
      le_trans
        (h3SpectralScalarRawFourierFifthMass_nonneg (W t i))
        hWi5m

  have hi0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t i)

  have hj0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t j)

  have hi5 :=
    h3SpectralScalarRawFourierFifthMass_nonneg (W t i)

  have hj5 :=
    h3SpectralScalarRawFourierFifthMass_nonneg (W t j)

  have hLeft :
      h3SpectralScalarRawFourierFifthMass (W t i) *
          h3SpectralScalarRawFourierL1Mass (W t j)
        ≤
      h3SelectedMildFifthMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul
      hWi5m
      hWj0
      hj0
      hM5nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W t i) *
          h3SpectralScalarRawFourierFifthMass (W t j)
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFifthMomentEnvelope ν A t :=
    mul_le_mul
      hWi0
      hWj5m
      hj5
      hM0nonneg

  have hSum :=
    add_le_add hLeft hRight

  have hCoeff0 :
      0 ≤ h3FourierFifthSplitCoefficient :=
    h3FourierFifthSplitCoefficient_nonneg

  unfold h3SelectedProductConvolutionFifthMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum hCoeff0)

end
end Euclidean
end Bridge
end PrimeTensor
