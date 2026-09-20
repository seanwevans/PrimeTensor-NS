import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Second.Derivative.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Second.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Second.Coordinate.Lag.Continuity

/-!
# Classicalization: forcing second-Fréchet coordinate time continuity

The selected instantaneous forcing difference is already continuous in the
second weighted raw-Fourier `L¹` topology:

    ∫ |ξ|² |N̂(W(r),W(r)) - N̂(W(s),W(s))| → 0.

At zero heat lag, one ordered forcing Hessian coordinate is exactly the inverse
Fourier transform of

    d_a(ξ) d_b(ξ) N̂(W(t),W(t))(ξ).

This file proves the corresponding zero-lag pointwise difference estimate

    |D²N_r[e_a,e_b] - D²N_s[e_a,e_b]|
      ≤ (2π)²
        ∫ |ξ|² |N̂_r - N̂_s|,

and combines it with the already-closed weighted difference limit.

Thus every fixed ordered canonical-coordinate evaluation of the instantaneous
forcing Hessian is time-continuous on the strict positive restart interval.

No new nonlinear estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingSecondFrechetTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Zero-lag mixed forcing-coordinate reconstruction is Lipschitz in the
second weighted raw-Fourier difference mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_selectedRestart_sub_le_differenceSecondMass
    {ν A r s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hr : 0 < r)
    (hrR : r ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν 0 (W r) (W r) i a b x
        -
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν 0 (W s) (W s) i a b x‖
      ≤
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Fr : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W r) (W r) i

  let Fs : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  let Kr : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν 0 (W r) (W r) i a b x

  let Ks : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
      ν 0 (W s) (W s) i a b x

  let R : H3FourierPoint3 → ℝ :=
    fun ξ => ‖ξ‖ ^ 2 * ‖Fr ξ - Fs ξ‖

  have hFr0 :
      Integrable Fr
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W r) (W r) i

  have hFs0 :
      Integrable Fs
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hFr2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fr ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFs2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ hs hsR i

  have hRawDiff0 :
      Integrable
        (fun ξ : H3FourierPoint3 => Fr ξ - Fs ξ)
        (volume : Measure H3FourierPoint3) :=
    hFr0.sub hFs0

  have hRawMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 2 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFr2.add hFs2

  have hRMeas :
      AEStronglyMeasurable R
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    exact
      (continuous_norm.pow 2).aestronglyMeasurable.mul
        hRawDiff0.aestronglyMeasurable.norm

  have hRPoint :
      ∀ ξ : H3FourierPoint3,
        R ξ
          ≤
        ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
    intro ξ
    dsimp only [R]
    calc
      ‖ξ‖ ^ 2 * ‖Fr ξ - Fs ξ‖
          ≤
        ‖ξ‖ ^ 2 * (‖Fr ξ‖ + ‖Fs ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (Fr ξ) (Fs ξ))
        (by positivity)
      _ =
        ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
        ring

  have hR :
      Integrable R
        (volume : Measure H3FourierPoint3) := by
    refine hRawMajor.mono' hRMeas ?_
    filter_upwards with ξ
    have hLeft0 : 0 ≤ R ξ := by
      dsimp only [R]
      positivity
    have hRight0 :
        0 ≤
          ‖ξ‖ ^ 2 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 2 * ‖Fs ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hRPoint ξ

  have hKr :
      Integrable Kr
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Kr]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-x)]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W r) (W r) i
    ]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ hr hrR i a b

  have hKs :
      Integrable Ks
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Ks]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-x)]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W s) (W s) i
    ]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ hs hsR i a b

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 * R ξ)
        (volume : Measure H3FourierPoint3) :=
    hR.const_mul ((2 * Real.pi) ^ 2)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖Kr ξ - Ks ξ‖
          ≤
        (2 * Real.pi) ^ 2 * R ξ := by
    intro ξ
    dsimp only [Kr, Ks, R, Fr, Fs]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateFourierKernel
    rw [← smul_sub]
    simp only [Circle.norm_smul]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateAmplitude
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero,
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
    ]

    have hAlg :
        h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ)
            -
            h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ)
          =
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ)) := by
      ring

    rw [hAlg, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

    have hRaw0 :
        0 ≤
          ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ :=
      norm_nonneg _

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg (norm_nonneg _) hRaw0)
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb hRaw0)
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ =
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

  rw [
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_eq_integral_kernel
  ]

  calc
    ‖(∫ ξ : H3FourierPoint3, Kr ξ) -
        ∫ ξ : H3FourierPoint3, Ks ξ‖
        =
      ‖∫ ξ : H3FourierPoint3, Kr ξ - Ks ξ‖ := by
        rw [integral_sub hKr hKs]
    _ ≤
      ∫ ξ : H3FourierPoint3, ‖Kr ξ - Ks ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3, (2 * Real.pi) ^ 2 * R ξ := by
        refine integral_mono_ae (hKr.sub hKs).norm hMajor ?_
        exact Filter.Eventually.of_forall hPoint
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3, R ξ) := by
        rw [integral_const_mul]
    _ =
      (2 * Real.pi) ^ 2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        rfl

/-- Every fixed ordered canonical-coordinate evaluation of the selected
instantaneous forcing Hessian is time-continuous at every strict positive
interior restart time. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_secondFrechet_coordinate_continuousAt_time
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W r) (W r) i)
          x
          ![ea, eb])
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let F : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 2
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W r) (W r) i)
        x
        ![ea, eb]

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖

  have hMass :
      Tendsto M (𝓝 s) (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceSecondMass_tendsto_zero
        hν U₀ hA hU₀ hs hsR i

  have hCoeff :
      Tendsto
        (fun _r : ℝ => ((2 * Real.pi) ^ 2 : ℝ))
        (𝓝 s)
        (𝓝 ((2 * Real.pi) ^ 2)) :=
    tendsto_const_nhds

  have hUpperTend :
      Tendsto
        (fun r : ℝ => (2 * Real.pi) ^ 2 * M r)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [mul_zero] using hCoeff.mul hMass

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hBound :
      ∀ᶠ r in 𝓝 s,
        ‖F r - F s‖
          ≤
        (2 * Real.pi) ^ 2 * M r := by
    filter_upwards [hInterior] with r hr

    have hEr :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
        hν U₀ hA hU₀ hr.1 hr.2.le i a b x

    have hEs :=
      h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
        hν U₀ hA hU₀ hs hsR.le i a b x

    have hBase :=
      norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_selectedRestart_sub_le_differenceSecondMass
        hν U₀ hA hU₀
        hr.1 hr.2.le
        hs hsR.le
        i a b x

    dsimp only [F, M, W, ea, eb] at hEr hEs hBase ⊢
    rw [← hEr, ← hEs]
    exact hBase

  have hNonneg :
      ∀ᶠ r in 𝓝 s,
        0 ≤ ‖F r - F s‖ :=
    Filter.Eventually.of_forall
      (fun r => norm_nonneg (F r - F s))

  have hNorm :
      Tendsto
        (fun r : ℝ => ‖F r - F s‖)
        (𝓝 s)
        (𝓝 0) :=
    squeeze_zero'
      hNonneg
      hBound
      hUpperTend

  change
    Tendsto F (𝓝 s) (𝓝 (F s))

  exact
    tendsto_iff_norm_sub_tendsto_zero.2 hNorm

end

end Euclidean
end Bridge
end PrimeTensor
