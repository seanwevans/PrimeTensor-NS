import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.QuadraticTimeContinuity

/-!
# Classicalization: quadratic Fourier control of the second Frechet derivative

`QuadraticTimeContinuity` proves that the selected positive-time restart path
is continuous in the quadratic weighted raw-Fourier difference mass

    M₂(W(r) - W(s)).

This file transports that topology to the complete second Frechet derivative
of the ordinary Fourier reconstruction.

Mathlib's explicit Fourier derivative formula gives

    D² 𝓕(f)
      = 𝓕(fourierPowSMulRight innerSL f 2),

and the multiplier satisfies the pointwise operator-norm estimate

    ‖fourierPowSMulRight innerSL f ξ 2‖
      ≤ (2π ‖innerSL‖)² ‖ξ‖² |f ξ|.

Consequently, for one fixed constant `C₂` independent of the evaluation point,

    ‖D² 𝓕(raw(H))(x)‖ ≤ C₂ M₂(H).

Applying this to `H = W(r)_i - W(s)_i` and the already-closed quadratic
difference-mass continuity yields convergence to zero of the complete second
Frechet derivative of the Fourier transform of the selected difference state.

This is the exact order-two analogue of the existing cubic Frechet transport.
No new Navier--Stokes or endpoint estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- Keep the Fourier carrier definitionally aligned with the generic moment
algebra and the preceding quadratic continuity file. -/
noncomputable local instance axisFintypeH3SchwartzClassicalizationQuadraticFrechetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Fixed operator-norm coefficient in the second Fourier derivative estimate. -/
noncomputable def h3QuadraticFourierSecondFrechetCoefficient : ℝ :=
  (2 * Real.pi *
      ‖(innerSL ℝ :
        H3FourierPoint3 →L[ℝ] H3FourierPoint3 →L[ℝ] ℝ)‖) ^ 2

theorem h3QuadraticFourierSecondFrechetCoefficient_nonneg :
    0 ≤ h3QuadraticFourierSecondFrechetCoefficient := by
  unfold h3QuadraticFourierSecondFrechetCoefficient
  positivity

/-- Numeral-normalized order-two moment weight. -/
theorem h3FourierMomentWeight_two_classicalization_quadraticFrechet
    (ξ : H3FourierPoint3) :
    h3FourierMomentWeight (2 : ℝ) ξ = ‖ξ‖ ^ 2 := by
  have h := h3FourierMomentWeight_natCast 2 ξ
  norm_num at h
  exact h

/-- Cubic moment integrability implies quadratic moment integrability. -/
theorem h3RawFourierMomentIntegrable_two_of_three
    (H : H3SpectralScalarState)
    (hThree : H3RawFourierMomentIntegrable (3 : ℝ) H) :
    H3RawFourierMomentIntegrable (2 : ℝ) H := by
  have hWeight3 :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
    intro ξ
    exact h3FourierMomentWeight_natCast 3 ξ

  have hThreeOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    unfold H3RawFourierMomentIntegrable at hThree
    refine hThree.congr ?_
    filter_upwards with ξ
    rw [hWeight3 ξ]

  have hRaw0 :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 H)

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier H)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      axisFintypeH3SchwartzClassicalizationQuadraticFrechetContinuity,
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
          ‖h3SpectralScalarRawFourier H ξ‖
            +
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRawNorm.add hThreeOrd

  have hLeftMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 2).aestronglyMeasurable.mul
      hRawNorm.aestronglyMeasurable

  have hTwoOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hLeftMeas ?_
    filter_upwards with ξ

    have hWeight :=
      norm_pow_two_le_one_add_pow_three ξ

    have hNorm0 :
        0 ≤ ‖h3SpectralScalarRawFourier H ξ‖ :=
      norm_nonneg _

    have hMul :=
      mul_le_mul_of_nonneg_right hWeight hNorm0

    have hLeft0 :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier H ξ‖ :=
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) 2)
        hNorm0

    rw [Real.norm_eq_abs, abs_of_nonneg hLeft0]

    calc
      ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖
          ≤
        (1 + ‖ξ‖ ^ 3) *
          ‖h3SpectralScalarRawFourier H ξ‖ :=
        hMul
      _ =
        ‖h3SpectralScalarRawFourier H ξ‖
          +
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
        ring

  unfold H3RawFourierMomentIntegrable
  refine hTwoOrd.congr ?_
  filter_upwards with ξ
  rw [h3FourierMomentWeight_two_classicalization_quadraticFrechet ξ]

/-- Quadratic weighted integrability supplies every natural Fourier moment
required by Mathlib's second derivative formula. -/
theorem h3SpectralScalarRawFourier_natMoment_integrable_le_two_of_quadratic
    (H : H3SpectralScalarState)
    (hTwo : H3RawFourierMomentIntegrable (2 : ℝ) H)
    (n : ℕ)
    (hn : n ≤ 2) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ n *
          ‖h3SpectralScalarRawFourier H ξ‖)
      (volume : Measure H3FourierPoint3) := by
  by_cases hn1 : n ≤ 1
  · exact
      h3SpectralScalarRawFourier_moment_integrable_one
        H n hn1

  have hn2 : n = 2 := by
    omega

  subst n

  unfold H3RawFourierMomentIntegrable at hTwo
  refine hTwo.congr ?_
  filter_upwards with ξ
  rw [h3FourierMomentWeight_two_classicalization_quadraticFrechet ξ]

/-- Quantitative second-Frechet-derivative transport from quadratic raw
Fourier mass.  The coefficient is independent of the spatial evaluation
point. -/
theorem h3SpectralScalarRawFourier_fourier_secondFrechet_norm_le
    (H : H3SpectralScalarState)
    (hTwo : H3RawFourierMomentIntegrable (2 : ℝ) H)
    (x : H3FourierPoint3) :
    ‖iteratedFDeriv ℝ 2
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
      ≤
    h3QuadraticFourierSecondFrechetCoefficient *
      h3SpectralScalarRawFourierMomentMass (2 : ℝ) H := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarRawFourier H

  have hMom :
      ∀ (n : ℕ), n ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn2 : n ≤ 2 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarRawFourier_natMoment_integrable_le_two_of_quadratic
        H hTwo n hn2

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

  have hTwoOrd :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hMom 2 (by norm_num)

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    innerSL ℝ

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 2

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hTwoOrd hRawMeas

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
            L f ξ 2‖
          ≤
        C * (‖ξ‖ ^ 2 * ‖f ξ‖) := by
    intro ξ
    have h :=
      VectorFourier.norm_fourierPowSMulRight_le
        L f ξ 2
    dsimp only [C]
    nlinarith [h]

  have hIntegralBound :
      (∫ ξ : H3FourierPoint3,
          ‖VectorFourier.fourierPowSMulRight
            L f ξ 2‖)
        ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖f ξ‖ := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      hPowInt.norm
      (hTwoOrd.const_mul C)
    exact Filter.Eventually.of_forall hPoint

  have hFourierNorm :
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 2)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 2‖ := by
    change
      ‖VectorFourier.fourierIntegral
          Real.fourierChar
          volume
          L.toLinearMap₁₂
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 2)
          x‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 2‖
    exact
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar
        volume
        L.toLinearMap₁₂
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2)
        x

  have hDeriv :
      iteratedFDeriv ℝ 2
          (FourierTransform.fourier f)
        =
      FourierTransform.fourier
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2) := by
    dsimp only [L]
    exact
      Real.iteratedFDeriv_fourier
        hMom hRawMeas (by norm_num)

  have hMass :
      h3SpectralScalarRawFourierMomentMass (2 : ℝ) H
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier H ξ‖ := by
    unfold h3SpectralScalarRawFourierMomentMass
    apply integral_congr_ae
    filter_upwards with ξ
    rw [h3FourierMomentWeight_two_classicalization_quadraticFrechet ξ]

  calc
    ‖iteratedFDeriv ℝ 2
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier H)) x‖
        =
      ‖FourierTransform.fourier
          (fun ξ : H3FourierPoint3 =>
            VectorFourier.fourierPowSMulRight
              L f ξ 2)
          x‖ := by
        dsimp only [f]
        rw [hDeriv]
    _ ≤
      ∫ ξ : H3FourierPoint3,
        ‖VectorFourier.fourierPowSMulRight
          L f ξ 2‖ :=
      hFourierNorm
    _ ≤
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖f ξ‖ :=
      hIntegralBound
    _ =
      h3QuadraticFourierSecondFrechetCoefficient *
        h3SpectralScalarRawFourierMomentMass
          (2 : ℝ) H := by
      dsimp only [C, L, f]
      rw [hMass]
      rfl

/-- Along every selected coordinate path, the complete second Frechet
derivative of the Fourier transform of the raw difference state tends to zero
at each strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_secondFrechet_difference_norm_tendsto_zero
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
        ‖iteratedFDeriv ℝ 2
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
    h3QuadraticFourierSecondFrechetCoefficient

  have hMassTendsto :
      Tendsto
        (fun r : ℝ =>
          h3SpectralScalarRawFourierMomentMass
            (2 : ℝ) (W r i - W s i))
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_quadraticDifferenceMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hScaledTendsto :
      Tendsto
        (fun r : ℝ =>
          C *
            h3SpectralScalarRawFourierMomentMass
              (2 : ℝ) (W r i - W s i))
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
        ‖iteratedFDeriv ℝ 2
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (W r i - W s i)))
          x‖
          ≤
        C *
          h3SpectralScalarRawFourierMomentMass
            (2 : ℝ) (W r i - W s i) := by
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
      refine hrThreeOrd.congr ?_
      filter_upwards with ξ
      have hWeight3 :
          h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
        have h := h3FourierMomentWeight_natCast 3 ξ
        norm_num at h
        exact h
      dsimp only [W]
      rw [hWeight3]

    have hsThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W s i) := by
      unfold H3RawFourierMomentIntegrable
      refine hsThreeOrd.congr ?_
      filter_upwards with ξ
      have hWeight3 :
          h3FourierMomentWeight (3 : ℝ) ξ = ‖ξ‖ ^ 3 := by
        have h := h3FourierMomentWeight_natCast 3 ξ
        norm_num at h
        exact h
      dsimp only [W]
      rw [hWeight3]

    have hDiffThree :
        H3RawFourierMomentIntegrable
          (3 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_three_sub
        (W r i) (W s i) hrThree hsThree

    have hDiffTwo :
        H3RawFourierMomentIntegrable
          (2 : ℝ) (W r i - W s i) :=
      h3RawFourierMomentIntegrable_two_of_three
        (W r i - W s i) hDiffThree

    dsimp only [C]
    exact
      h3SpectralScalarRawFourier_fourier_secondFrechet_norm_le
        (W r i - W s i) hDiffTwo x

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc (norm_nonneg _))

  · intro ε hε

    have hScaledEventually :
        ∀ᶠ r in 𝓝 s,
          C *
              h3SpectralScalarRawFourierMomentMass
                (2 : ℝ) (W r i - W s i)
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
