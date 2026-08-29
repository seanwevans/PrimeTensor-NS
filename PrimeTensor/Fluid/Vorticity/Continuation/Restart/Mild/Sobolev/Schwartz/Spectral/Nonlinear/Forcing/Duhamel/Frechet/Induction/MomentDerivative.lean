import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentConvolution

/-!
# Fréchet endpoint induction: generic derivative moments

The nonlinear forcing spends exactly one Fourier power on divergence.  This
file records that loss once for an arbitrary nonnegative real exponent `q`.

If the exact raw product convolution carries moment `q + 1`, then one Fourier
derivative carries moment `q`:

    m_q(D_j(F̂ * Ĝ))
      ≤
    (2π) m_{q+1}(F̂ * Ĝ).

Combining with the generic Young estimate from `MomentConvolution` gives the
fully quantitative bound

    m_q(D_j(F̂ * Ĝ))
      ≤
    (2π) 2^(q+1)
      (m_{q+1}(F)m_0(G) + m_0(F)m_{q+1}(G)).

This replaces all later named `DerivativeMass` checkpoints.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic `q`-moment mass after one Fourier derivative hits an exact raw
product convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionMomentMass
    (q : ℝ)
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierMomentWeight q ξ *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- One derivative converts an integrable convolution moment `q+1` into an
integrable derivative moment `q`. -/
theorem h3FourierDerivative_mul_rawProductConvolution_moment_integrable_of_nextMoment
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConvNext :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hq).aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierMomentWeight (q + 1) ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConvNext.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hWq :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hTargetNonneg :
      0 ≤
        h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ :=
    mul_nonneg hWq (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    exact
      mul_nonneg
        (by positivity)
        (mul_nonneg
          (h3FourierMomentWeight_nonneg (q + 1) ξ)
          (norm_nonneg _))

  have hBound :
      h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (h3FourierMomentWeight (q + 1) ξ *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierMomentWeight q ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierMomentWeight q ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hWq
      _ =
        (2 * Real.pi) *
          ((h3FourierMomentWeight q ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierMomentWeight_add_one hq ξ]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the next raw convolution moment. -/
theorem h3FourierDerivativeRawProductConvolutionMomentMass_le
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConvNext :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionMomentMass q F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionMomentMass (q + 1) F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_moment_integrable_of_nextMoment
      hq F G j hConvNext

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (h3FourierMomentWeight (q + 1) ξ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConvNext.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierMomentWeight q ξ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    have hWq :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    calc
      h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        h3FourierMomentWeight q ξ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierMomentWeight q ξ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          hWq
      _ =
        (2 * Real.pi) *
          ((h3FourierMomentWeight q ξ * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring
      _ =
        (2 * Real.pi) *
          (h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [h3FourierMomentWeight_add_one hq ξ]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionMomentMass
  unfold h3RawProductConvolutionMomentMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (q + 1) ξ *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of generic `(q+1)` state
moments and the unweighted `L¹` masses. -/
theorem h3FourierDerivativeRawProductConvolutionMomentMass_le_stateMasses
    {q : ℝ}
    (hq : 0 ≤ q)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hFNext : H3RawFourierMomentIntegrable (q + 1) F)
    (hGNext : H3RawFourierMomentIntegrable (q + 1) G) :
    h3FourierDerivativeRawProductConvolutionMomentMass q F G j
      ≤
    (2 * Real.pi) *
      (h3FourierMomentSplitCoefficient (q + 1) *
        (h3SpectralScalarRawFourierMomentMass (q + 1) F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierMomentMass (q + 1) G)) := by
  have hqNext : 0 ≤ q + 1 := by
    linarith

  have hConvNext :=
    h3RawProductConvolution_moment_integrable_of
      hqNext F G hFNext hGNext

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionMomentMass_le
      hq F G j hConvNext

  have hConvMass :=
    h3RawProductConvolutionMomentMass_le
      hqNext F G hFNext hGNext

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

end
end Euclidean
end Bridge
end PrimeTensor
