import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarter.Convolution.Mass.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarterDerivative

/-!
# Quantitative five-quarter mass after one Fourier derivative

`FiveQuarterDerivative` already proves qualitatively that one Fourier
derivative spends exactly one power from a `9/4` convolution moment and leaves
an integrable `5/4` moment.

`NineQuarterConvolutionMassBound` now gives a numerical bound for the actual
`9/4` convolution mass.

This file records the quantitative scalar bridge:

    m₅(∂ⱼ(F * G))
      ≤
    2π · m₉(F * G),

and then composes it with the exact Young estimate

    m₉(F * G)
      ≤
    C₉ (m₉(F)m₀(G) + m₀(F)m₉(G)).

This is the scalar numerical inequality consumed by the later finite
divergence and Leray projection bounds.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFiveQuarterDerivativeMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `5/4` weighted `L¹` mass after applying one Fourier derivative to the
exact raw product convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionFiveQuarterMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFiveQuarterWeight ξ *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Pointwise quantitative derivative spending:
`5/4 + 1 = 9/4`, with Fourier derivative coefficient `2π`. -/
theorem h3FourierDerivative_mul_rawProductConvolution_fiveQuarter_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    h3FourierFiveQuarterWeight ξ *
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖
      ≤
    (2 * Real.pi) *
      (h3FourierNineQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖) := by
  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  calc
    h3FourierFiveQuarterWeight ξ *
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖
        =
      h3FourierFiveQuarterWeight ξ *
        (‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawProductConvolution F G ξ‖) := by
            rw [norm_mul]
    _ ≤
      h3FourierFiveQuarterWeight ξ *
        (((2 * Real.pi) * ‖ξ‖) *
          ‖h3RawProductConvolution F G ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          hDerivative
          (norm_nonneg _))
        hFive0
    _ =
      (2 * Real.pi) *
        ((h3FourierFiveQuarterWeight ξ * ‖ξ‖) *
          ‖h3RawProductConvolution F G ξ‖) := by
      ring
    _ =
      (2 * Real.pi) *
        (h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖) := by
      rw [h3FourierFiveQuarterWeight_mul_norm_eq_nineQuarterWeight]

/-- The actual `5/4` derivative-convolution mass is at most `2π` times the
actual `9/4` convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionFiveQuarterMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv9 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFiveQuarterMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionNineQuarterMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_fiveQuarterMoment_integrable_of_nineQuarterMoment
      F G j hConv9

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierNineQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv9.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierFiveQuarterWeight ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
    Filter.Eventually.of_forall
      (h3FourierDerivative_mul_rawProductConvolution_fiveQuarter_le
        F G j)

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionFiveQuarterMass
  unfold h3RawProductConvolutionNineQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
      rw [integral_const_mul]

/-- Fully quantitative scalar forcing bound obtained by composing one
derivative spend with the exact `9/4` Young convolution estimate. -/
theorem h3FourierDerivativeRawProductConvolutionFiveQuarterMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
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
    h3FourierDerivativeRawProductConvolutionFiveQuarterMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierNineQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierNineQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierNineQuarterMass G)) := by
  have hConv9 :=
    h3RawProductConvolution_nineQuarterMoment_integrable_of
      F G hFq hGq

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionFiveQuarterMass_le
      F G j hConv9

  have hConvMass :=
    h3RawProductConvolutionNineQuarterMass_le
      F G hFq hGq

  have hTwoPi0 : 0 ≤ 2 * Real.pi := by
    positivity

  calc
    h3FourierDerivativeRawProductConvolutionFiveQuarterMass F G j
        ≤
      (2 * Real.pi) *
        h3RawProductConvolutionNineQuarterMass F G :=
      hDerivative
    _ ≤
      (2 * Real.pi) *
        (h3FourierNineQuarterSplitCoefficient *
          (h3SpectralScalarRawFourierNineQuarterMass F *
              h3SpectralScalarRawFourierL1Mass G +
            h3SpectralScalarRawFourierL1Mass F *
              h3SpectralScalarRawFourierNineQuarterMass G)) :=
      mul_le_mul_of_nonneg_left hConvMass hTwoPi0

end
end Euclidean
end Bridge
end PrimeTensor
