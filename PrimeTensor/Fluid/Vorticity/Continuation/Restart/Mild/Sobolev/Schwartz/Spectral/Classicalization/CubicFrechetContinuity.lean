import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.CubicTimeContinuity

/-!
# Classicalization: cubic Fourier control of the third Frechet derivative

`CubicTimeContinuity` proves that the selected positive-time path is continuous
in the cubic weighted raw-Fourier difference mass

    M₃(F(r) - F(s)).

This file transports that topology one step closer to the classical third
spatial jet.

Mathlib's explicit Fourier derivative formula writes the third Frechet
derivative of the Fourier transform as the Fourier transform of the cubic
multilinear multiplier. Its operator norm is bounded pointwise by

    (2 π ‖innerSL‖)³ ‖ξ‖³ |f(ξ)|.

Consequently

    ‖D³ 𝓕(raw(H))(x)‖
      ≤ C_F M₃(H)

for one fixed Fourier constant `C_F`, uniformly in `x`.

Applying this to `H = W(r)_i - W(s)_i` and using the compiled cubic
difference-mass continuity gives convergence of the complete third Frechet
derivative to zero for the difference state.

The remaining bridge is finite-dimensional bookkeeping: compose with spatial
negation for the inverse Fourier transform, evaluate the third multilinear map
on the three coordinate directions, and identify that value with the ordered
`spatial3.d` jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Keep the Fourier carrier definitionally aligned with the generic moment
algebra and the preceding classicalization files. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Fixed operator-norm coefficient in the third Fourier derivative estimate. -/
noncomputable def h3CubicFourierThirdFrechetCoefficient : ℝ :=
  (2 * Real.pi *
      ‖(innerSL ℝ :
        H3FourierPoint3 →L[ℝ] H3FourierPoint3 →L[ℝ] ℝ)‖) ^ 3

theorem h3CubicFourierThirdFrechetCoefficient_nonneg :
    0 ≤ h3CubicFourierThirdFrechetCoefficient := by
  unfold h3CubicFourierThirdFrechetCoefficient
  positivity

/-- Explicit numeral-normalized form of the generic natural-moment weight at
order three.  Keeping this named avoids Lean having to infer that the real
literal `3` is the cast of the natural `3` at every boundary. -/
theorem h3FourierMomentWeight_three_classicalization_cubicFrechet
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
  have h := h3FourierMomentWeight_natCast 3 ξ
  norm_num at h
  exact h

/-- Cubic weighted integrability plus the ambient H³ raw `L¹` fact supplies
the only missing lower natural moment, order two. Thus every natural moment
through order three is available to Mathlib's third Fourier derivative
formula. -/
theorem h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (n : ℕ)
    (hn : n ≤ 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hThree' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hThree
    refine hThree.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  by_cases hn1 : n ≤ 1
  · exact
      h3SpectralScalarRawFourier_moment_integrable_one
        H n hn1

  have hn23 : n = 2 ∨ n = 3 := by
    omega

  rcases hn23 with rfl | rfl

  · have hRaw0 :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 H)

    have hRaw :
        Integrable
          (h3SpectralScalarRawFourier H)
          (volume : Measure H3FourierPoint3) := by
      simpa only [
        axisFintypeH3SchwartzClassicalizationCubicFrechetContinuity,
        axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
        axisFintypeH3SpectralL1,
        axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
      ] using hRaw0

    have hRawNorm :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3SpectralScalarRawFourier H ξ‖)
          (volume : Measure H3FourierPoint3) :=
      hRaw.norm

    have hMajor :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖h3SpectralScalarRawFourier H ξ‖ +
              ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier H ξ‖)
          (volume : Measure H3FourierPoint3) :=
      hRawNorm.add hThree'

    have hLeftMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier H ξ‖)
          (volume : Measure H3FourierPoint3) :=
      (continuous_norm.pow 2).aestronglyMeasurable.mul
        hRawNorm.aestronglyMeasurable

    refine hMajor.mono' hLeftMeas ?_
    exact Filter.Eventually.of_forall (fun ξ => by
      have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

      have hPow :
          ‖ξ‖ ^ 2 ≤ 1 + ‖ξ‖ ^ 3 := by
        by_cases hx : ‖ξ‖ ≤ 1
        · have hGap : 0 ≤ 1 - ‖ξ‖ :=
            sub_nonneg.mpr hx
          have hQuadGap :
              0 ≤ ‖ξ‖ * (1 - ‖ξ‖) :=
            mul_nonneg hx0 hGap
          have h30 : 0 ≤ ‖ξ‖ ^ 3 :=
            pow_nonneg hx0 3
          nlinarith
        · have hx1 : 1 ≤ ‖ξ‖ :=
            le_of_lt (lt_of_not_ge hx)
          have h20 : 0 ≤ ‖ξ‖ ^ 2 :=
            pow_nonneg hx0 2
          have h23 :
              ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 3 := by
            calc
              ‖ξ‖ ^ 2 = ‖ξ‖ ^ 2 * 1 := by ring
              _ ≤ ‖ξ‖ ^ 2 * ‖ξ‖ :=
                mul_le_mul_of_nonneg_left hx1 h20
              _ = ‖ξ‖ ^ 3 := by ring
          linarith

      have hNorm0 :
          0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
        norm_nonneg _

      have hMul :=
        mul_le_mul_of_nonneg_right hPow hNorm0

      have hLeft0 :
          0 ≤
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier H ξ‖ :=
        mul_nonneg (pow_nonneg hx0 2) hNorm0

      rw [Real.norm_eq_abs, abs_of_nonneg hLeft0]
      calc
        ‖ξ‖ ^ 2 * ‖h3SpectralScalarRawFourier H ξ‖
            ≤
          (1 + ‖ξ‖ ^ 3) *
            ‖h3SpectralScalarRawFourier H ξ‖ :=
          hMul
        _ =
          ‖h3SpectralScalarRawFourier H ξ‖ +
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier H ξ‖ := by
          ring)

  · exact hThree'

/-- Cubic weighted raw-Fourier integrability is stable under subtraction of
spectral states. -/
theorem h3RawFourierMomentIntegrable_three_sub
    (F G : H3SpectralScalarState)
    (hF : H3RawFourierMomentIntegrable (3 : ℝ) F)
    (hG : H3RawFourierMomentIntegrable (3 : ℝ) G) :
    H3RawFourierMomentIntegrable (3 : ℝ) (F - G) := by
  have hF' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF
    refine hF.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  have hG' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG
    refine hG.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationCubicFrechetContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSubAE0

  have hRawSub0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (F - G))

  have hRawSub :
      Integrable
        (h3SpectralScalarRawFourier (F - G))
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationCubicFrechetContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSub0

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF'.add hG'

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 3).aestronglyMeasurable.mul
      hRawSub.norm.aestronglyMeasurable

  have hOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      rw [hξ]
      have hWeight0 : 0 ≤ ‖ξ‖ ^ 3 :=
        pow_nonneg (norm_nonneg ξ) 3
      have hTri :=
        norm_sub_le
          (h3SpectralScalarRawFourier F ξ)
          (h3SpectralScalarRawFourier G ξ)
      have hMul :=
        mul_le_mul_of_nonneg_left hTri hWeight0
      have hLeft0 :
          0 ≤
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ :=
        mul_nonneg hWeight0 (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hLeft0]
      calc
        ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F ξ -
              h3SpectralScalarRawFourier G ξ‖
            ≤
          ‖ξ‖ ^ 3 *
            (‖h3SpectralScalarRawFourier F ξ‖ +
              ‖h3SpectralScalarRawFourier G ξ‖) :=
          hMul
        _ =
          ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 3 * ‖h3SpectralScalarRawFourier G ξ‖ := by
          ring)

  unfold H3RawFourierMomentIntegrable
  refine hOrd.congr ?_
  filter_upwards with ξ
  rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

/-- Quantitative third-Frechet-derivative transport from cubic raw Fourier
mass. The coefficient is independent of the spatial evaluation point. -/
theorem h3SpectralScalarRawFourier_fourier_thirdFrechet_norm_le
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H)
    (x : H3FourierPoint3) :
    ‖iteratedFDeriv ℝ 3
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
      ≤
    h3CubicFourierThirdFrechetCoefficient *
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  have hMom :
      ∀ (n : ℕ), n ≤ (3 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn3 : n ≤ 3 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarRawFourier_natMoment_integrable_le_three_of_cubic
        H hThree n hn3

  have hRawInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 H)

  have hRawMeas :
      AEStronglyMeasurable f
        (volume : Measure H3FourierPoint3) :=
    hRawInt.aestronglyMeasurable

  have hThreeOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hMom 3 (by norm_num)

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    innerSL ℝ

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 3

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 3)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hThreeOrd hRawMeas

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
            L f ξ 3‖
          ≤
        C * (‖ξ‖ ^ 3 * ‖f ξ‖) := by
    intro ξ
    have h :=
      VectorFourier.norm_fourierPowSMulRight_le
        L f ξ 3
    dsimp only [C]
    nlinarith [h]

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖VectorFourier.fourierPowSMulRight
            L f ξ 3‖)
        ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖f ξ‖ := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      hPowInt.norm
      (hThreeOrd.const_mul C)
    exact Filter.Eventually.of_forall hPoint

  have hFourierNorm :
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 3)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 3‖ := by
    change
      ‖VectorFourier.fourierIntegral
          Real.fourierChar
          volume
          L.toLinearMap₁₂
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 3)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 3‖
    exact
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar
        volume
        L.toLinearMap₁₂
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 3)
        x

  have hDeriv :
      iteratedFDeriv ℝ 3
          (FourierTransform.fourier f)
        =
      FourierTransform.fourier
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 3) := by
    dsimp only [L]
    exact
      Real.iteratedFDeriv_fourier
        hMom hRawMeas (by norm_num)

  have hMass :
      h3SpectralScalarRawFourierMomentMass (3 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [h3FourierMomentWeight_three_classicalization_cubicFrechet ξ]

  calc
    ‖iteratedFDeriv ℝ 3
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
        =
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 3)
          x‖ := by
        dsimp only [f]
        rw [hDeriv]
    _ ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 3‖ :=
      hFourierNorm
    _ ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖f ξ‖ :=
      hIntegralBound
    _ =
      h3CubicFourierThirdFrechetCoefficient *
        h3SpectralScalarRawFourierMomentMass
          (3 : ℝ) H := by
      dsimp only [C, L, f]
      rw [hMass]
      rfl

/-- Along every selected coordinate path, the complete third Frechet
derivative of the Fourier transform of the raw difference state tends to zero
at each strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_thirdFrechet_difference_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 3
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r i
                -
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s i)))
          x‖)
      (𝓝 s)
      (𝓝 0) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let C : ℝ :=
    h3CubicFourierThirdFrechetCoefficient

  have hMassTendsto :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_cubicDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hScaledTendsto :
      Tendsto
        (fun r : ℝ =>
          C *
            h3SpectralScalarRawFourierMomentMass
              (3 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℝ => C)
          (𝓝 s)
          (𝓝 C) :=
      tendsto_const_nhds
    have hMul :=
      hConst.mul hMassTendsto
    simpa only [mul_zero] using hMul

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hBoundEventually :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 3
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          x‖
          ≤
        C *
          h3SpectralScalarRawFourierMomentMass
            (3 : ℝ) (W r i - W s i) := by
    filter_upwards [hInterval] with r hr

    have hrThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsThreeOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        3 hν U₀ hA hU₀ hs hsR.le i

    have hrThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hrThreeOrd

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_three_classicalization_cubicFrechet
      ] using hsThreeOrd

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    dsimp only [C]
    exact
      h3SpectralScalarRawFourier_fourier_thirdFrechet_norm_le
        (W r i - W s i) hDiffThree x

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc (norm_nonneg _))

  · intro ε hε

    have hScaledEventually :
        ∀ᶠ r in 𝓝 s,
          C *
              h3SpectralScalarRawFourierMomentMass
                (3 : ℝ) (W r i - W s i)
            < ε :=
      (tendsto_order.1 hScaledTendsto).2 ε hε

    filter_upwards
      [hBoundEventually, hScaledEventually]
      with r hBound hScaled

    exact lt_of_le_of_lt hBound hScaled

end
end Euclidean
end Bridge
end PrimeTensor
