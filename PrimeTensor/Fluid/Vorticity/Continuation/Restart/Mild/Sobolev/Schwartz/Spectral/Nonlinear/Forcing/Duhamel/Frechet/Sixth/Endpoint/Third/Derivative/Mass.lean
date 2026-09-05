import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fourth.Convolution.Mass

/-!
# Sixth Fréchet endpoint: quantitative third derivative mass

The selected quadratic product convolution now has a quantitative full fourth
raw Fourier moment.  The nonlinear forcing spends exactly one Fourier power on
divergence, leaving

    4 - 1 = 3.

This file isolates that scalar derivative step.

The key exact radial identity is

    |ξ|^3 |ξ| = |ξ|^4.

Together with

    ‖D_j(ξ)‖ ≤ (2π)|ξ|,

it gives

    m₃(D_j(F̂ * Ĝ))
      ≤
    (2π) m₄(F̂ * Ĝ).

The final theorems specialize this estimate to two coordinates of the selected
positive-time mild state, using the selected fourth convolution envelope from
`FourthConvolutionMass`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointThirdDerivativeMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Spending one ordinary radial power on the cubic weight gives the fourth
weight exactly. -/
theorem h3FourierThirdWeight_mul_norm_eq_fourth
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3 * ‖ξ‖
      =
    ‖ξ‖ ^ 4 := by
  ring

/-- Cubic raw Fourier mass after one derivative hits an exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionThirdMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 3 *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one Fourier derivative on an integrable fourth convolution leaves
an integrable cubic moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_thirdMoment_integrable_of_fourthMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 3).aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 4 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv4.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hW3 :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hW3 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg
          (pow_nonneg (norm_nonneg ξ) 4)
          (norm_nonneg _))

  have hBound :
      ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ ^ 4 *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 3 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 3 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW3
      _ =
        (2 * Real.pi) *
          ((‖ξ‖ ^ 3 * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierThirdWeight_mul_norm_eq_fourth]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the fourth raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionThirdMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionThirdMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionFourthMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_thirdMoment_integrable_of_fourthMoment
      F G j hConv4

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 4 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv4.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 3 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    have hW3 :
        0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3

    calc
      ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 3 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 3 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW3
      _ =
        (2 * Real.pi) *
          ((‖ξ‖ ^ 3 * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierThirdWeight_mul_norm_eq_fourth]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionThirdMass
  unfold h3RawProductConvolutionFourthMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of fourth and unweighted
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionThirdMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionThirdMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierFourthSplitCoefficient *
        (h3SpectralScalarRawFourierFourthMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFourthMass G)) := by
  have hConv4 :=
    h3RawProductConvolution_fourthMoment_integrable_of
      F G hF4 hG4

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionThirdMass_le
      F G j hConv4

  have hConvMass :=
    h3RawProductConvolutionFourthMass_le
      F G hF4 hG4

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

/-- Selected scalar derivative cubic envelope. -/
noncomputable def h3SelectedDerivativeThirdMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  (2 * Real.pi) *
    h3SelectedProductConvolutionFourthMomentEnvelope ν A t

/-- Every selected positive-time scalar derivative-convolution term has an
integrable cubic moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_selectedRestart_thirdMoment_integrable
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
        ‖ξ‖ ^ 3 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  exact
    h3FourierDerivative_mul_rawProductConvolution_thirdMoment_integrable_of_fourthMoment
      (W t i) (W t j) j hConv4

/-- Every selected positive-time scalar derivative-convolution term has cubic
mass bounded by the selected derivative envelope. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_thirdMass_le
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
    h3FourierDerivativeRawProductConvolutionThirdMass
        (W t i) (W t j) j
      ≤
    h3SelectedDerivativeThirdMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionThirdMass_le
      (W t i) (W t j) j hConv4

  have hConvBound :
      h3RawProductConvolutionFourthMass (W t i) (W t j)
        ≤
      h3SelectedProductConvolutionFourthMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fourthMass_le
        hν U₀ hA hU₀ ht htR i j

  unfold h3SelectedDerivativeThirdMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hConvBound
        (by positivity))

end
end Euclidean
end Bridge
end PrimeTensor
