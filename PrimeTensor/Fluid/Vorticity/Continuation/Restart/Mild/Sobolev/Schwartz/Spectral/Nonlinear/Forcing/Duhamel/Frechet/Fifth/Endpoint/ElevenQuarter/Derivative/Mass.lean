import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarter.Convolution.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Second.Forcing.Mass

/-!
# Fifth Fréchet endpoint: quantitative eleven-quarter derivative mass

The selected quadratic product convolution now has a quantitative `15/4`
raw Fourier moment.  The nonlinear forcing spends exactly one Fourier power
on divergence, leaving

    15/4 - 1 = 11/4.

This file isolates that scalar derivative step.

The key exact radial identity is

    |ξ|^(11/4) |ξ| = |ξ|^(15/4).

Together with

    ‖D_j(ξ)‖ ≤ (2π)|ξ|,

it gives

    m_{11/4}(D_j(F̂ * Ĝ))
      ≤
    (2π) m_{15/4}(F̂ * Ĝ).

The final theorem specializes this estimate to two coordinates of the
selected positive-time mild state, using the selected `15/4` convolution
envelope from `FifteenQuarterConvolutionMass`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointElevenQuarterDerivativeMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radial `11/4` Fourier weight. -/
noncomputable def h3FourierElevenQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((11 : ℝ) / 4)

/-- Spending one ordinary radial power on the `11/4` weight gives the
`15/4` weight exactly. -/
theorem h3FourierElevenQuarterWeight_mul_norm_eq_fifteenQuarter
    (ξ : H3FourierPoint3) :
    h3FourierElevenQuarterWeight ξ * ‖ξ‖
      =
    h3FourierFifteenQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierElevenQuarterWeight
    h3FourierFifteenQuarterWeight

  calc
    ‖ξ‖ ^ ((11 : ℝ) / 4) * ‖ξ‖
        =
      ‖ξ‖ ^ ((11 : ℝ) / 4) *
        ‖ξ‖ ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ =
      ‖ξ‖ ^ (((11 : ℝ) / 4) + 1) := by
      rw [
        ← Real.rpow_add_of_nonneg
          hξ0
          (by norm_num : 0 ≤ (11 : ℝ) / 4)
          (by norm_num : 0 ≤ (1 : ℝ))
      ]
    _ =
      ‖ξ‖ ^ ((15 : ℝ) / 4) := by
      congr 1
      ring

/-- `11/4` raw Fourier mass after one derivative hits an exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionElevenQuarterMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierElevenQuarterWeight ξ *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one Fourier derivative on an integrable `15/4` convolution leaves
an integrable `11/4` moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_elevenQuarterMoment_integrable_of_fifteenQuarterMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hWeightContinuous :
      Continuous h3FourierElevenQuarterWeight := by
    unfold h3FourierElevenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (11 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierFifteenQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv15.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hW11 :
      0 ≤ h3FourierElevenQuarterWeight ξ := by
    unfold h3FourierElevenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hW11 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg
          (by
            unfold h3FourierFifteenQuarterWeight
            exact Real.rpow_nonneg (norm_nonneg ξ) _)
          (norm_nonneg _))

  have hBound :
      h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (h3FourierFifteenQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierElevenQuarterWeight ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierElevenQuarterWeight ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW11
      _ =
        (2 * Real.pi) *
          ((h3FourierElevenQuarterWeight ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierElevenQuarterWeight_mul_norm_eq_fifteenQuarter]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the `15/4` raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionElevenQuarterMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionElevenQuarterMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionFifteenQuarterMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_elevenQuarterMoment_integrable_of_fifteenQuarterMoment
      F G j hConv15

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierFifteenQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv15.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierElevenQuarterWeight ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    have hW11 :
        0 ≤ h3FourierElevenQuarterWeight ξ := by
      unfold h3FourierElevenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierElevenQuarterWeight ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierElevenQuarterWeight ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hW11
      _ =
        (2 * Real.pi) *
          ((h3FourierElevenQuarterWeight ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierElevenQuarterWeight_mul_norm_eq_fifteenQuarter]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionElevenQuarterMass
  unfold h3RawProductConvolutionFifteenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of `15/4` and unweighted
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionElevenQuarterMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionElevenQuarterMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierFifteenQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierFifteenQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierFifteenQuarterMass G)) := by
  have hConv15 :=
    h3RawProductConvolution_fifteenQuarterMoment_integrable_of
      F G hF15 hG15

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionElevenQuarterMass_le
      F G j hConv15

  have hConvMass :=
    h3RawProductConvolutionFifteenQuarterMass_le
      F G hF15 hG15

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

/-- Selected scalar derivative `11/4` envelope. -/
noncomputable def h3SelectedDerivativeElevenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  (2 * Real.pi) *
    h3SelectedProductConvolutionFifteenQuarterMomentEnvelope ν A t

/-- Every selected positive-time scalar derivative-convolution term has an
integrable `11/4` moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_selectedRestart_elevenQuarterMoment_integrable
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
        h3FourierElevenQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  exact
    h3FourierDerivative_mul_rawProductConvolution_elevenQuarterMoment_integrable_of_fifteenQuarterMoment
      (W t i) (W t j) j hConv15

/-- Every selected positive-time scalar derivative-convolution term has
`11/4` mass bounded by the selected derivative envelope. -/
theorem h3FourierDerivativeRawProductConvolution_selectedRestart_elevenQuarterMass_le
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
    h3FourierDerivativeRawProductConvolutionElevenQuarterMass
        (W t i) (W t j) j
      ≤
    h3SelectedDerivativeElevenQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hConv15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  have hBase :=
    h3FourierDerivativeRawProductConvolutionElevenQuarterMass_le
      (W t i) (W t j) j hConv15

  have hConvBound :
      h3RawProductConvolutionFifteenQuarterMass (W t i) (W t j)
        ≤
      h3SelectedProductConvolutionFifteenQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawProductConvolution_selectedRestart_fifteenQuarterMass_le
        hν U₀ hA hU₀ ht htR i j

  unfold h3SelectedDerivativeElevenQuarterMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left
        hConvBound
        (by positivity))

end
end Euclidean
end Bridge
end PrimeTensor
