import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Seventh.Endpoint.FifthConvolutionMass

/-!
# Seventh Fréchet endpoint: quantitative fourth derivative mass

The selected quadratic product convolution now has a quantitative full fifth
raw Fourier moment. The nonlinear forcing spends exactly one Fourier power on
divergence, leaving

    5 - 1 = 4.

This file isolates that scalar derivative step.

The key exact radial identity is

    |ξ|^4 |ξ| = |ξ|^5.

Together with

    ‖D_j(ξ)‖ ≤ (2π)|ξ|,

it gives

    m₄(D_j(F̂ * Ĝ))
      ≤
    (2π) m₅(F̂ * Ĝ).

The final theorems specialize this estimate to two coordinates of the selected
positive-time mild state, using the selected fifth convolution envelope from
`FifthConvolutionMass`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSeventhEndpointFourthDerivativeMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Spending one ordinary radial power on the fourth weight gives the fifth
weight exactly. -/
theorem h3FourierFourthWeight_mul_norm_eq_fifth
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 4 * ‖ξ‖
      =
    ‖ξ‖ ^ 5 := by
  ring

/-- Fourth raw Fourier mass after one derivative hits an exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionFourthMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 4 *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one Fourier derivative on an integrable fifth convolution leaves
an integrable fourth moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_fourthMoment_integrable_of_fifthMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 5 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv5.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hW4 :
      0 ≤ ‖ξ‖ ^ 4 :=
    pow_nonneg (norm_nonneg ξ) 4

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hW4 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg
          (pow_nonneg (norm_nonneg ξ) 5)
          (norm_nonneg _))

  have hBound :
      ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ ^ 5 *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 4 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 4 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW4
      _ =
        (2 * Real.pi) *
          ((‖ξ‖ ^ 4 * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierFourthWeight_mul_norm_eq_fifth]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the fifth raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionFourthMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFourthMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionFifthMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_fourthMoment_integrable_of_fifthMoment
      F G j hConv5

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 5 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv5.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 4 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    have hW4 :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg (norm_nonneg ξ) 4

    calc
      ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 4 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 4 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW4
      _ =
        (2 * Real.pi) *
          ((‖ξ‖ ^ 4 * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierFourthWeight_mul_norm_eq_fifth]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionFourthMass
  unfold h3RawProductConvolutionFifthMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of fifth and unweighted
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionFourthMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFourthMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierFifthSplitCoefficient *
        (h3SpectralScalarRawFourierFifthMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFifthMass G)) := by
  have hConv5 :=
    h3RawProductConvolution_fifthMoment_integrable_of
      F G hF5 hG5

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionFourthMass_le
      F G j hConv5

  have hConvMass :=
    h3RawProductConvolutionFifthMass_le
      F G hF5 hG5

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

/-- Selected scalar derivative fourth-moment envelope. -/
noncomputable def h3SelectedDerivativeFourthMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  (2 * Real.pi) *
    h3SelectedProductConvolutionFifthMomentEnvelope ν A t

/-- Every selected positive-time scalar derivative-convolution term has an
integrable fourth moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_selectedRestart_fourthMoment_integrable
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
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  exact
    h3FourierDerivative_mul_rawProductConvolution_fourthMoment_integrable_of_fifthMoment
      (W t i) (W t j) j hConv5

/-- Every selected positive-time scalar derivative-convolution term has fourth
mass bounded by the selected derivative envelope. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_fourthMass_le
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
    h3FourierDerivativeRawProductConvolutionFourthMass
        (W t i) (W t j) j
      ≤
    h3SelectedDerivativeFourthMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionFourthMass_le
      (W t i) (W t j) j hConv5

  have hConvBound :
      h3RawProductConvolutionFifthMass (W t i) (W t j)
        ≤
      h3SelectedProductConvolutionFifthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifthMass_le
        hν U₀ hA hU₀ ht htR i j

  unfold h3SelectedDerivativeFourthMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hConvBound
        (by positivity))

end
end Euclidean
end Bridge
end PrimeTensor
