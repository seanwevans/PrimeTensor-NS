import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedConvolutionNineQuarter
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFirst

/-!
# Spending one derivative from a nine-quarter convolution moment

`SelectedConvolutionNineQuarter` gives an integrable `9/4` Fourier moment for
each exact raw product convolution of the selected positive-time mild state.

The nonlinear forcing spends exactly one Fourier derivative.  This file
isolates the corresponding scalar weighted estimate.

Define

    w₅(ξ) = ‖ξ‖^(5/4).

Since

    w₅(ξ) * ‖ξ‖ = ‖ξ‖^(9/4),

and

    ‖∂̂ⱼ(ξ)‖ ≤ 2π ‖ξ‖,

an integrable `9/4` convolution moment immediately yields an integrable `5/4`
moment after multiplication by one Fourier derivative.

This is the only new analytic step needed before lifting the result through the
finite outer-product divergence and Leray projection.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFiveQuarterDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The residual Fourier weight after spending one derivative from `9/4`. -/
noncomputable def h3FourierFiveQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((5 : ℝ) / 4)

/-- Spending one power of frequency turns the `5/4` residual weight exactly
into the `9/4` convolution weight. -/
theorem h3FourierFiveQuarterWeight_mul_norm_eq_nineQuarterWeight
    (ξ : H3FourierPoint3) :
    h3FourierFiveQuarterWeight ξ * ‖ξ‖
      =
    h3FourierNineQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  unfold h3FourierFiveQuarterWeight
  unfold h3FourierNineQuarterWeight

  calc
    ‖ξ‖ ^ ((5 : ℝ) / 4) * ‖ξ‖
        =
      ‖ξ‖ ^ ((5 : ℝ) / 4) * ‖ξ‖ ^ (1 : ℝ) := by
        rw [Real.rpow_one]
    _ =
      ‖ξ‖ ^ (((5 : ℝ) / 4) + 1) := by
        rw [
          ← Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (5 : ℝ) / 4)
            (by norm_num : 0 ≤ (1 : ℝ))
        ]
    _ =
      ‖ξ‖ ^ ((9 : ℝ) / 4) := by
        congr 1
        ring

/-- A single Fourier derivative spends one power of a `9/4` convolution moment
and leaves an integrable `5/4` moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_fiveQuarterMoment_integrable_of_nineQuarterMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv9 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hWeightContinuous :
      Continuous h3FourierFiveQuarterWeight := by
    unfold h3FourierFiveQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (5 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierNineQuarterWeight ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv9.const_mul (2 * Real.pi)

  refine hMajorant.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hNine0 :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierFiveQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hFive0 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (h3FourierNineQuarterWeight ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg hNine0 (norm_nonneg _))

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hBound :
      h3FourierFiveQuarterWeight ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖) := by
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

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

end
end Euclidean
end Bridge
end PrimeTensor
