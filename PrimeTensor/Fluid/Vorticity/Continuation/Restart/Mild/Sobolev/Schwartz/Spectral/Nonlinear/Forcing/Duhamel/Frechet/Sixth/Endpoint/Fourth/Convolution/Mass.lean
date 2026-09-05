import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fourth.Convolution.Majorant.Mass

/-!
# Sixth Fréchet endpoint: quantitative fourth mass of the exact raw convolution

`FourthConvolutionMajorantMass` computes the exact total mass of the scalar
fourth-moment Young majorant.  This file exposes the corresponding pointwise
domination of the actual complex raw product convolution:

    |ξ|^4 |(F̂ * Ĝ)(ξ)|
      ≤
    M₄(F,G)(ξ)

for almost every frequency.

Integrating gives

    m₄(F * G)
      ≤
    2^4 (m₄(F)m₀(G) + m₀(F)m₄(G)).

The final theorem specializes both inputs to coordinates of the selected mild
state, using the newly closed canonical selected fourth-moment state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointFourthConvolutionMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution fourth weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionFourthMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 4 *
      ‖h3RawProductConvolution F G ξ‖

/-- The scalar fourth-moment convolution majorant is pointwise nonnegative. -/
theorem h3RawProductConvolutionFourthMomentMajorant_nonneg
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    0 ≤ h3RawProductConvolutionFourthMomentMajorant F G ξ := by
  have hLeft :
      0 ≤ h3RawProductConvolutionFourthMomentLeftMajorant F G ξ := by
    unfold h3RawProductConvolutionFourthMomentLeftMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (mul_nonneg
            (pow_nonneg (norm_nonneg η) 4)
            (norm_nonneg _))
          (norm_nonneg _)

  have hRight :
      0 ≤ h3RawProductConvolutionFourthMomentRightMajorant F G ξ := by
    unfold h3RawProductConvolutionFourthMomentRightMajorant
    exact
      integral_nonneg fun η =>
        mul_nonneg
          (norm_nonneg _)
          (mul_nonneg
            (pow_nonneg (norm_nonneg (ξ - η)) 4)
            (norm_nonneg _))

  unfold h3RawProductConvolutionFourthMomentMajorant
  exact
    mul_nonneg
      h3FourierFourthSplitCoefficient_nonneg
      (add_nonneg hLeft hRight)

/-- The exact raw convolution is dominated almost everywhere by the fourth
Young majorant whose mass was computed in the previous checkpoint. -/
theorem h3RawProductConvolution_fourthMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionFourthMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f4 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 4 *
        ‖h3SpectralScalarRawFourier F η‖

  let g4 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 4 *
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
          f4 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF4.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f4, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g4 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG4
    simpa only [
      f0, g4,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f4 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g4 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ ‖ξ‖ ^ 4 :=
    pow_nonneg (norm_nonneg ξ) 4

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
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (‖ξ‖ ^ 4)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFourthSplitCoefficient *
            (f4 η * g0 (ξ - η) +
              f0 η * g4 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierFourthSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierFourthSplitCoefficient *
          (f4 η * g0 (ξ - η) +
            f0 η * g4 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierFourthWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        ‖ξ‖ ^ 4 *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
        rw [norm_mul]
      _ ≤
        (h3FourierFourthSplitCoefficient *
          (‖η‖ ^ 4 + ‖ξ - η‖ ^ 4)) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right
          hFreq hProdNonneg
      _ =
        h3FourierFourthSplitCoefficient *
          (f4 η * g0 (ξ - η) +
            f0 η * g4 (ξ - η)) := by
        dsimp only [f0, g0, f4, g4]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierFourthSplitCoefficient *
          (f4 η * g0 (ξ - η) +
            f0 η * g4 (ξ - η)) :=
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
    ‖ξ‖ ^ 4 *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      ‖ξ‖ ^ 4 *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left
        hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierFourthSplitCoefficient *
          (f4 η * g0 (ξ - η) +
            f0 η * g4 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionFourthMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionFourthMomentMajorant
      unfold h3RawProductConvolutionFourthMomentLeftMajorant
      unfold h3RawProductConvolutionFourthMomentRightMajorant
      dsimp only [f0, g0, f4, g4]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- The exact raw product convolution inherits an integrable fourth Fourier
moment from fourth moments on both input raw representatives. -/
theorem h3RawProductConvolution_fourthMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMajor :=
    h3RawProductConvolutionFourthMomentMajorant_integrable
      F G hF4 hG4

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
      (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  have hDom :=
    h3RawProductConvolution_fourthMoment_le_majorant_ae
      F G hF4 hG4

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hDom] with ξ hξ

  have hTarget0 :
      0 ≤
        ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖ :=
    mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 4)
      (norm_nonneg _)

  have hMajor0 :
      0 ≤
        h3RawProductConvolutionFourthMomentMajorant F G ξ :=
    h3RawProductConvolutionFourthMomentMajorant_nonneg
      F G ξ

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0,
    abs_of_nonneg hMajor0
  ] using hξ

/-- Numerical fourth weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionFourthMass_le
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionFourthMass F G
      ≤
    h3FourierFourthSplitCoefficient *
      (h3SpectralScalarRawFourierFourthMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFourthMass G) := by
  have hTarget :=
    h3RawProductConvolution_fourthMoment_integrable_of
      F G hF4 hG4

  have hMajor :=
    h3RawProductConvolutionFourthMomentMajorant_integrable
      F G hF4 hG4

  have hDom :=
    h3RawProductConvolution_fourthMoment_le_majorant_ae
      F G hF4 hG4

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFourthMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionFourthMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFourthMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierFourthSplitCoefficient *
        (h3SpectralScalarRawFourierFourthMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFourthMass G) :=
      h3RawProductConvolutionFourthMomentMajorant_integral_eq
        F G hF4 hG4

/-- Selected diagonal fourth raw-product-convolution envelope. -/
noncomputable def h3SelectedProductConvolutionFourthMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3FourierFourthSplitCoefficient *
    (h3SelectedMildFourthMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A +
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFourthMomentEnvelope ν A t)

/-- Every selected positive-time scalar product convolution has an integrable
fourth raw Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_fourthMoment_integrable
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
        ‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  exact
    h3RawProductConvolution_fourthMoment_integrable_of
      _
      _
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i)
      (h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR j)

/-- Every selected positive-time scalar product convolution has its fourth raw
Fourier mass bounded by the explicit selected state envelope. -/
theorem h3RawProductConvolution_selectedRestart_fourthMass_le
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
    h3RawProductConvolutionFourthMass
        (W t i) (W t j)
      ≤
    h3SelectedProductConvolutionFourthMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hWi4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (W t i) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hWj4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR j

  have hBase :=
    h3RawProductConvolutionFourthMass_le
      (W t i) (W t j) hWi4 hWj4

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

  have hWi4m :
      h3SpectralScalarRawFourierFourthMass (W t i)
        ≤
      h3SelectedMildFourthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le
        hν U₀ hA hU₀ ht htR i

  have hWj4m :
      h3SpectralScalarRawFourierFourthMass (W t j)
        ≤
      h3SelectedMildFourthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fourthMass_le
        hν U₀ hA hU₀ ht htR j

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM4nonneg :
      0 ≤ h3SelectedMildFourthMomentEnvelope ν A t := by
    exact
      le_trans
        (h3SpectralScalarRawFourierFourthMass_nonneg (W t i))
        hWi4m

  have hi0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t i)

  have hj0 :=
    h3SpectralScalarRawFourierL1Mass_nonneg (W t j)

  have hi4 :=
    h3SpectralScalarRawFourierFourthMass_nonneg (W t i)

  have hj4 :=
    h3SpectralScalarRawFourierFourthMass_nonneg (W t j)

  have hLeft :
      h3SpectralScalarRawFourierFourthMass (W t i) *
          h3SpectralScalarRawFourierL1Mass (W t j)
        ≤
      h3SelectedMildFourthMomentEnvelope ν A t *
        h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul
      hWi4m
      hWj0
      hj0
      hM4nonneg

  have hRight :
      h3SpectralScalarRawFourierL1Mass (W t i) *
          h3SpectralScalarRawFourierFourthMass (W t j)
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
        h3SelectedMildFourthMomentEnvelope ν A t :=
    mul_le_mul
      hWi0
      hWj4m
      hj4
      hM0nonneg

  have hSum :=
    add_le_add hLeft hRight

  have hCoeff0 :
      0 ≤ h3FourierFourthSplitCoefficient :=
    h3FourierFourthSplitCoefficient_nonneg

  unfold h3SelectedProductConvolutionFourthMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum hCoeff0)

end
end Euclidean
end Bridge
end PrimeTensor
