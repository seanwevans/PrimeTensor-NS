import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Time.Continuity
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Classicalization: quartic Fourier control of the fourth Fréchet derivative

`QuarticTimeContinuity` proves continuity of the selected positive-time path in
the quartic weighted raw-Fourier difference mass

    M₄(F(r) - F(s)).

Mathlib's explicit Fourier derivative formula writes the fourth Fréchet
derivative of the Fourier transform as the Fourier transform of the quartic
multilinear multiplier. Its operator norm is bounded pointwise by

    (2 π ‖innerSL‖)⁴ ‖ξ‖⁴ |f(ξ)|.

Consequently

    ‖D⁴ 𝓕(raw(H))(x)‖
      ≤ C_F M₄(H),

uniformly in `x`.

Applying this to the selected difference state and using quartic difference
mass continuity gives convergence to zero of the complete fourth Fourier
Fréchet derivative.

The inverse-Fourier/C¹ representative bookkeeping is deliberately left to the
next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuarticFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

noncomputable def h3QuarticFourierFourthFrechetCoefficient : ℝ :=
  (2 * Real.pi *
      ‖(innerSL ℝ :
        H3FourierPoint3 →L[ℝ] H3FourierPoint3 →L[ℝ] ℝ)‖) ^ 4

theorem h3QuarticFourierFourthFrechetCoefficient_nonneg :
    0 ≤ h3QuarticFourierFourthFrechetCoefficient := by
  unfold h3QuarticFourierFourthFrechetCoefficient
  positivity

theorem h3FourierMomentWeight_four_classicalization_quarticFrechet
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (4 : ℝ) ξ = ‖ξ‖ ^ 4 := by
  have h := h3FourierMomentWeight_natCast 4 ξ
  norm_num at h
  exact h

private theorem norm_pow_le_one_add_pow_four_quarticFrechet
    (ξ : H3FourierPoint3)
    (n : ℕ)
    (hn : n ≤ 4) :
    ‖ξ‖ ^ n ≤ 1 + ‖ξ‖ ^ 4 := by
  have hx0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  by_cases hx1 : ‖ξ‖ ≤ 1
  · have hpow :
        ‖ξ‖ ^ n ≤ (1 : ℝ) ^ n :=
      pow_le_pow_left₀ hx0 hx1 n
    have hpowOne : ‖ξ‖ ^ n ≤ 1 := by
      simpa using hpow
    exact
      hpowOne.trans
        (le_add_of_nonneg_right
          (pow_nonneg hx0 4))
  · have hx1' : 1 ≤ ‖ξ‖ :=
      le_of_lt (lt_of_not_ge hx1)
    have hpow :
        ‖ξ‖ ^ n ≤ ‖ξ‖ ^ 4 :=
      pow_le_pow_right₀ hx1' hn
    exact
      le_add_of_nonneg_of_le
        zero_le_one hpow

/-- Quartic weighted integrability plus raw `L¹` controls every natural moment
through order four. -/
theorem h3SpectralScalarRawFourier_natMoment_integrable_le_four_of_quartic
    (H : H3SpectralScalarState)
    (hFour : H3RawFourierMomentIntegrable (4 : ℝ) H)
    (n : ℕ)
    (hn : n ≤ 4) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hFour' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hFour
    refine hFour.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_four_classicalization_quarticFrechet ξ]

  have hRaw0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuarticFrechetContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRaw0

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier H ξ‖ +
            ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.add hFour'

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow n).aestronglyMeasurable.mul
      hRaw.norm.aestronglyMeasurable

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hWeight :=
    norm_pow_le_one_add_pow_four_quarticFrechet ξ n hn

  have hPoint :
      ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖
        ≤
      (1 + ‖ξ‖ ^ 4) *
        ‖h3SpectralScalarRawFourier H ξ‖ :=
    mul_le_mul_of_nonneg_right
      hWeight
      (norm_nonneg _)

  have hTarget0 :
      0 ≤
        ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖ := by
    positivity

  change
    ‖(‖ξ‖ ^ n *
      ‖h3SpectralScalarRawFourier H ξ‖ : ℝ)‖
      ≤
    ‖h3SpectralScalarRawFourier H ξ‖ +
      ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier H ξ‖

  rw [Real.norm_eq_abs, abs_of_nonneg hTarget0]
  calc
    ‖ξ‖ ^ n * ‖h3SpectralScalarRawFourier H ξ‖
        ≤
      (1 + ‖ξ‖ ^ 4) *
        ‖h3SpectralScalarRawFourier H ξ‖ := hPoint
    _ =
      ‖h3SpectralScalarRawFourier H ξ‖ +
        ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
      ring

/-- Quartic weighted raw-Fourier integrability is stable under subtraction. -/
theorem h3RawFourierMomentIntegrable_four_sub
    (F G : H3SpectralScalarState)
    (hF : H3RawFourierMomentIntegrable (4 : ℝ) F)
    (hG : H3RawFourierMomentIntegrable (4 : ℝ) G) :
    H3RawFourierMomentIntegrable (4 : ℝ) (F - G) := by
  have hF' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hF
    refine hF.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_four_classicalization_quarticFrechet ξ]

  have hG' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hG
    refine hG.congr ?_
    filter_upwards with ξ
    rw [h3FourierMomentWeight_four_classicalization_quarticFrechet ξ]

  have hRawSubAE0 :=
    h3SpectralScalarRawFourier_sub_ae F G

  have hRawSubAE :
      h3SpectralScalarRawFourier (F - G)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3SpectralScalarRawFourier F ξ -
          h3SpectralScalarRawFourier G ξ) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuarticFrechetContinuity,
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
      axisFintypeH3SchwartzClassicalizationQuarticFrechetContinuity,
      axisFintypeH3SchwartzFrechetInductionMomentAlgebra,
      axisFintypeH3SpectralL1,
      axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    ] using hRawSub0

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF'.add hG'

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
      hRawSub.norm.aestronglyMeasurable

  have hOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier (F - G) ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    exact hRawSubAE.mono (fun ξ hξ => by
      rw [hξ]
      have hWeight0 : 0 ≤ ‖ξ‖ ^ 4 :=
        pow_nonneg (norm_nonneg ξ) 4
      have hTri :=
        norm_sub_le
          (h3SpectralScalarRawFourier F ξ)
          (h3SpectralScalarRawFourier G ξ)
      have hMul :=
        mul_le_mul_of_nonneg_left hTri hWeight0
      have hLeft0 :
          0 ≤
            ‖ξ‖ ^ 4 *
              ‖h3SpectralScalarRawFourier F ξ -
                h3SpectralScalarRawFourier G ξ‖ := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hLeft0]
      calc
        ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F ξ -
              h3SpectralScalarRawFourier G ξ‖
            ≤
          ‖ξ‖ ^ 4 *
            (‖h3SpectralScalarRawFourier F ξ‖ +
              ‖h3SpectralScalarRawFourier G ξ‖) :=
          hMul
        _ =
          ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier F ξ‖ +
            ‖ξ‖ ^ 4 * ‖h3SpectralScalarRawFourier G ξ‖ := by
          ring)

  unfold H3RawFourierMomentIntegrable
  refine hOrd.congr ?_
  filter_upwards with ξ
  rw [h3FourierMomentWeight_four_classicalization_quarticFrechet ξ]

/-- Quantitative fourth-Fréchet-derivative transport from quartic raw Fourier
mass. -/
theorem h3SpectralScalarRawFourier_fourier_fourthFrechet_norm_le
    (H : H3SpectralScalarState)
    (hFour : H3RawFourierMomentIntegrable (4 : ℝ) H)
    (x : H3FourierPoint3) :
    ‖iteratedFDeriv ℝ 4
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
      ≤
    h3QuarticFourierFourthFrechetCoefficient *
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) H := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  have hMom :
      ∀ (n : ℕ), n ≤ (4 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn4 : n ≤ 4 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarRawFourier_natMoment_integrable_le_four_of_quartic
        H hFour n hn4

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

  have hFourOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hMom 4 (by norm_num)

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    innerSL ℝ

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 4

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFourOrd hRawMeas

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
            L f ξ 4‖
          ≤
        C * (‖ξ‖ ^ 4 * ‖f ξ‖) := by
    intro ξ
    have h :=
      VectorFourier.norm_fourierPowSMulRight_le
        L f ξ 4
    dsimp only [C]
    nlinarith [h]

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖VectorFourier.fourierPowSMulRight
            L f ξ 4‖)
        ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖f ξ‖ := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      hPowInt.norm
      (hFourOrd.const_mul C)
    exact Filter.Eventually.of_forall hPoint

  have hFourierNorm :
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 4)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 4‖ := by
    change
      ‖VectorFourier.fourierIntegral
          Real.fourierChar
          volume
          L.toLinearMap₁₂
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 4)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 4‖
    exact
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar
        volume
        L.toLinearMap₁₂
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        x

  have hDeriv :
      iteratedFDeriv ℝ 4
          (FourierTransform.fourier f)
        =
      FourierTransform.fourier
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4) := by
    dsimp only [L]
    exact
      Real.iteratedFDeriv_fourier
        hMom hRawMeas (by norm_num)

  have hMass :
      h3SpectralScalarRawFourierMomentMass (4 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [h3FourierMomentWeight_four_classicalization_quarticFrechet ξ]

  calc
    ‖iteratedFDeriv ℝ 4
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
        =
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 4)
          x‖ := by
        dsimp only [f]
        rw [hDeriv]
    _ ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 4‖ :=
      hFourierNorm
    _ ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖f ξ‖ :=
      hIntegralBound
    _ =
      h3QuarticFourierFourthFrechetCoefficient *
        h3SpectralScalarRawFourierMomentMass
          (4 : ℝ) H := by
      dsimp only [C, L, f]
      rw [hMass]
      rfl

/-- Along every selected coordinate path, the complete fourth Fréchet
derivative of the Fourier transform of the raw difference state tends to zero
at each strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_fourthFrechet_difference_norm_tendsto_zero
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
        ‖iteratedFDeriv ℝ 4
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
    h3QuarticFourierFourthFrechetCoefficient

  have hMassTendsto :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (4 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quarticDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hScaledTendsto :
      Tendsto
        (fun r : ℝ =>
          C *
            h3SpectralScalarRawFourierMomentMass
              (4 : ℝ) (W r i - W s i))
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
        ‖iteratedFDeriv ℝ 4
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          x‖
          ≤
        C *
          h3SpectralScalarRawFourierMomentMass
            (4 : ℝ) (W r i - W s i) := by
    filter_upwards [hInterval] with r hr

    have hrFourOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsFourOrd :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        4 hν U₀ hA hU₀ hs hsR.le i

    have hrFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W r i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_four_classicalization_quarticFrechet
      ] using hrFourOrd

    have hsFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      simpa only [
        W,
        h3FourierMomentWeight_four_classicalization_quarticFrechet
      ] using hsFourOrd

    have hDiffFour :
        H3RawFourierMomentIntegrable
          (4 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_four_sub
        (W r i) (W s i) hrFour hsFour

    dsimp only [C]
    exact
      h3SpectralScalarRawFourier_fourier_fourthFrechet_norm_le
        (W r i - W s i) hDiffFour x

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc (norm_nonneg _))

  · intro ε hε

    have hScaledEventually :
        ∀ᶠ r in 𝓝 s,
          C *
              h3SpectralScalarRawFourierMomentMass
                (4 : ℝ) (W r i - W s i)
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
