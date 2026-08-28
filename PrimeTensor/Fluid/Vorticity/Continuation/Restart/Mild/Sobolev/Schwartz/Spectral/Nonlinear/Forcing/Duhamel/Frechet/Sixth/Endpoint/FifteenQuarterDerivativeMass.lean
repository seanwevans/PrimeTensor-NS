import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterConvolutionMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.SecondForcingMass

/-!
# Sixth Fréchet endpoint: quantitative fifteen-quarter derivative mass

The selected quadratic product convolution now has a quantitative `19/4`
raw Fourier moment. The nonlinear forcing spends exactly one Fourier power
on divergence, leaving

    19/4 - 1 = 15/4.

This file isolates that scalar derivative step.

The key exact radial identity is

    |ξ|^(15/4) |ξ| = |ξ|^(19/4).

Together with

    ‖D_j(ξ)‖ ≤ (2π)|ξ|,

it gives

    m_{15/4}(D_j(F̂ * Ĝ))
      ≤
    (2π) m_{19/4}(F̂ * Ĝ).

The final theorem specializes this estimate to two coordinates of the
selected positive-time mild state, using the selected `19/4` convolution
envelope from `NineteenQuarterConvolutionMass`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointFifteenQuarterDerivativeMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Spending one ordinary radial power on the `15/4` weight gives the
`19/4` weight exactly. -/
theorem h3FourierFifteenQuarterWeight_mul_norm_eq_nineteenQuarter
    (ξ : H3FourierPoint3) :
    h3FourierFifteenQuarterWeight ξ * ‖ξ‖
      =
    h3FourierNineteenQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierFifteenQuarterWeight
    h3FourierNineteenQuarterWeight

  calc
    ‖ξ‖ ^ ((15 : ℝ) / 4) * ‖ξ‖
        =
      ‖ξ‖ ^ ((15 : ℝ) / 4) *
        ‖ξ‖ ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ =
      ‖ξ‖ ^ (((15 : ℝ) / 4) + 1) := by
      rw [
        ← Real.rpow_add_of_nonneg
          hξ0
          (by norm_num : 0 ≤ (15 : ℝ) / 4)
          (by norm_num : 0 ≤ (1 : ℝ))
      ]
    _ =
      ‖ξ‖ ^ ((19 : ℝ) / 4) := by
      congr 1
      ring

/-- `15/4` raw Fourier mass after one derivative hits an exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFifteenQuarterWeight ξ *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one Fourier derivative on an integrable `19/4` convolution leaves
an integrable `15/4` moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_fifteenQuarterMoment_integrable_of_nineteenQuarterMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

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
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierNineteenQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv19.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hW15 :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hW15 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg
          (by
            unfold h3FourierNineteenQuarterWeight
            exact Real.rpow_nonneg (norm_nonneg ξ) _)
          (norm_nonneg _))

  have hBound :
      h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (h3FourierNineteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierFifteenQuarterWeight ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierFifteenQuarterWeight ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW15
      _ =
        (2 * Real.pi) *
          ((h3FourierFifteenQuarterWeight ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierFifteenQuarterWeight_mul_norm_eq_nineteenQuarter]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the `19/4` raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionFifteenQuarterMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionNineteenQuarterMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_fifteenQuarterMoment_integrable_of_nineteenQuarterMoment
      F G j hConv19

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierNineteenQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv19.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierFifteenQuarterWeight ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    have hW15 :
        0 ≤ h3FourierFifteenQuarterWeight ξ := by
      unfold h3FourierFifteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierFifteenQuarterWeight ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierFifteenQuarterWeight ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW15
      _ =
        (2 * Real.pi) *
          ((h3FourierFifteenQuarterWeight ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierFifteenQuarterWeight_mul_norm_eq_nineteenQuarter]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
  unfold h3RawProductConvolutionNineteenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of `19/4` and unweighted
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionFifteenQuarterMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierNineteenQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierNineteenQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierNineteenQuarterMass G)) := by
  have hConv19 :=
    h3RawProductConvolution_nineteenQuarterMoment_integrable_of
      F G hF19 hG19

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass_le
      F G j hConv19

  have hConvMass :=
    h3RawProductConvolutionNineteenQuarterMass_le
      F G hF19 hG19

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

/-- Selected scalar derivative `15/4` envelope. -/
noncomputable def h3SelectedDerivativeFifteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  (2 * Real.pi) *
    h3SelectedProductConvolutionNineteenQuarterMomentEnvelope ν A t

/-- Every selected positive-time scalar derivative-convolution term has an
integrable `15/4` moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_selectedRestart_fifteenQuarterMoment_integrable
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
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  exact
    h3FourierDerivative_mul_rawProductConvolution_fifteenQuarterMoment_integrable_of_nineteenQuarterMoment
      (W t i) (W t j) j hConv19

/-- Every selected positive-time scalar derivative-convolution term has
`15/4` mass bounded by the selected derivative envelope. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_fifteenQuarterMass_le
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
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass
        (W t i) (W t j) j
      ≤
    h3SelectedDerivativeFifteenQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv19 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionFifteenQuarterMass_le
      (W t i) (W t j) j hConv19

  have hConvBound :
      h3RawProductConvolutionNineteenQuarterMass (W t i) (W t j)
        ≤
      h3SelectedProductConvolutionNineteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_nineteenQuarterMass_le
        hν U₀ hA hU₀ ht htR i j

  unfold h3SelectedDerivativeFifteenQuarterMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hConvBound
        (by positivity))

end
end Euclidean
end Bridge
end PrimeTensor
