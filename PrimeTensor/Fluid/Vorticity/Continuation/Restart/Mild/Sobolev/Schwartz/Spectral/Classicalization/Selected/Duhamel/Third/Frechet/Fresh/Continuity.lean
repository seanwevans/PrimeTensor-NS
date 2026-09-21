import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Rescaled
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Heat.Third.Derivative.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Third.Difference.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.Third.Frechet.Time.Continuity

/-!
# Classicalization: third-Fréchet fresh-tail endpoint continuity

For one ordered coordinate triple `(a,b,c)` the rescaled fresh integrand is

    D_a D_b D_c H_{h(1-u)}
      N(W(t+hu),W(t+hu))(x).

The two endpoint effects are already separately controlled:

* fixed selected state, heat lag `τ ↓ 0`:
  `Selected.Forcing.Heat.Third.Derivative.Continuity`;
* moving selected state, cubic forcing-difference mass:
  `Selected.Forcing.Third.Difference.Continuity`.

Three coordinate symbols cost `(2π)^3 |ξ|^3`, while the heat multiplier is
contractive.  Hence changing the forcing state at any positive lag is bounded
uniformly by the unheated cubic forcing-difference mass.

Combining this moving-state estimate with the fixed-state heat endpoint gives
the pointwise rescaled fresh-integrand limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetFreshContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At positive heat lag, changing the selected forcing inputs is controlled by
the unheated cubic weighted Fourier mass of their forcing difference. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_sub_le_differenceThirdMass
    {ν A r s τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hr : 0 < r)
    (hrR : r ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (hτ : 0 < τ)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν τ (W r) (W r) i a b c x
        -
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν τ (W s) (W s) i a b c x‖
      ≤
    (2 * Real.pi) ^ 3 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
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
    h3RawFinLerayOuterProductDivergence (W r) (W r) i

  let Fs : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence (W s) (W s) i

  let KU : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
      ν τ (W r) (W r) i a b c x

  let KV : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
      ν τ (W s) (W s) i a b c x

  let R : H3FourierPoint3 → ℝ :=
    fun ξ => ‖ξ‖ ^ 3 * ‖Fr ξ - Fs ξ‖

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

  have hFr3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖Fr ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fr, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ hr hrR i

  have hFs3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Fs, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ hs hsR i

  have hRawDiff0 :
      Integrable
        (fun ξ : H3FourierPoint3 => Fr ξ - Fs ξ)
        (volume : Measure H3FourierPoint3) :=
    hFr0.sub hFs0

  have hRawMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 3 * ‖Fs ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFr3.add hFs3

  have hRMeas :
      AEStronglyMeasurable R
        (volume : Measure H3FourierPoint3) := by
    dsimp only [R]
    exact
      (continuous_norm.pow 3).aestronglyMeasurable.mul
        hRawDiff0.aestronglyMeasurable.norm

  have hRPoint :
      ∀ ξ : H3FourierPoint3,
        R ξ
          ≤
        ‖ξ‖ ^ 3 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 3 * ‖Fs ξ‖ := by
    intro ξ
    dsimp only [R]
    calc
      ‖ξ‖ ^ 3 * ‖Fr ξ - Fs ξ‖
          ≤
        ‖ξ‖ ^ 3 * (‖Fr ξ‖ + ‖Fs ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (Fr ξ) (Fs ξ))
        (by positivity)
      _ =
        ‖ξ‖ ^ 3 * ‖Fr ξ‖ +
          ‖ξ‖ ^ 3 * ‖Fs ξ‖ := by
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
          ‖ξ‖ ^ 3 * ‖Fr ξ‖ +
            ‖ξ‖ ^ 3 * ‖Fs ξ‖ := by
      positivity
    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hLeft0,
      abs_of_nonneg hRight0
    ] using hRPoint ξ

  have hKU :
      Integrable KU
        (volume : Measure H3FourierPoint3) := by
    dsimp only [KU]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-x)]

    have hHeat3 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ (W r) (W r) i ξ‖)
          (volume : Measure H3FourierPoint3) := by
      exact
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
          hν hτ (W r) (W r) i 3 (by norm_num)

    have hMeas :
        AEStronglyMeasurable
          (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν τ (W r) (W r) i a b c)
          (volume : Measure H3FourierPoint3) := by
      unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
      exact
        (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
              (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                ν τ (W r) (W r) i)))

    have hMajor :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 3 *
                ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                  ν τ (W r) (W r) i ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hHeat3.const_mul ((2 * Real.pi) ^ 3)

    refine hMajor.mono' hMeas ?_
    filter_upwards with ξ
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
        ν τ (W r) (W r) i a b c ξ

  have hKV :
      Integrable KV
        (volume : Measure H3FourierPoint3) := by
    dsimp only [KV]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-x)]

    have hHeat3 :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ (W s) (W s) i ξ‖)
          (volume : Measure H3FourierPoint3) := by
      exact
        h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
          hν hτ (W s) (W s) i 3 (by norm_num)

    have hMeas :
        AEStronglyMeasurable
          (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν τ (W s) (W s) i a b c)
          (volume : Measure H3FourierPoint3) := by
      unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
      exact
        (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
              (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                ν τ (W s) (W s) i)))

    have hMajor :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 3 *
                ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                  ν τ (W s) (W s) i ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hHeat3.const_mul ((2 * Real.pi) ^ 3)

    refine hMajor.mono' hMeas ?_
    filter_upwards with ξ
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
        ν τ (W s) (W s) i a b c ξ

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 * R ξ)
        (volume : Measure H3FourierPoint3) :=
    hR.const_mul ((2 * Real.pi) ^ 3)

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖KU ξ - KV ξ‖
          ≤
        (2 * Real.pi) ^ 3 * R ξ := by
    intro ξ
    dsimp only [KU, KV, R, Fr, Fs]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    rw [← smul_sub]
    simp only [Circle.norm_smul]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative

    have hAlg :
        h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                (h3FourierDerivativeSymbol c ξ *
                  (h3HeatFourierSymbol ν τ ξ *
                    h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ)))
            -
            h3FourierDerivativeSymbol a ξ *
              (h3FourierDerivativeSymbol b ξ *
                (h3FourierDerivativeSymbol c ξ *
                  (h3HeatFourierSymbol ν τ ξ *
                    h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ)))
          =
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              (h3HeatFourierSymbol ν τ ξ *
                (h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ)))) := by
      ring

    rw [hAlg, norm_mul, norm_mul, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
    have hc :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ

    have hRaw0 :
        0 ≤
          ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
            h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖ :=
      norm_nonneg _

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              (‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)))
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              (‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖))) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg
                (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) hRaw0)))
    _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              (‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖))) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg
                (norm_nonneg _)
                (mul_nonneg (norm_nonneg _) hRaw0)))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              (‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖))) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hc
                (mul_nonneg (norm_nonneg _) hRaw0))
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              (1 *
                ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
                  h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖))) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hHeat hRaw0)
                (by
                  unfold h3FourierGradientMagnitude
                  positivity))
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ =
        (2 * Real.pi) ^ 3 *
          (‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

  rw [
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_eq_integral_kernel,
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_eq_integral_kernel
  ]

  calc
    ‖(∫ ξ : H3FourierPoint3, KU ξ) -
        ∫ ξ : H3FourierPoint3, KV ξ‖
        =
      ‖∫ ξ : H3FourierPoint3, KU ξ - KV ξ‖ := by
        rw [integral_sub hKU hKV]
    _ ≤
      ∫ ξ : H3FourierPoint3, ‖KU ξ - KV ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3, (2 * Real.pi) ^ 3 * R ξ := by
        refine integral_mono_ae (hKU.sub hKV).norm hMajor ?_
        exact Filter.Eventually.of_forall hPoint
    _ =
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3, R ξ) := by
        rw [integral_const_mul]
    _ =
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence (W r) (W r) i ξ -
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖) := by
        rfl

/-- For every interior unit parameter, the rescaled third-Fréchet fresh
integrand tends jointly in vanishing heat lag and moving selected state to the
instantaneous forcing third-coordinate derivative. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t u : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t h W i a b c x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c)
          ])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let E : ℂ :=
    iteratedFDeriv ℝ 3
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖

  let T : ℝ → ℂ :=
    fun h =>
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν (h * (1 - u)) (W t) (W t) i a b c x

  let g : ℝ → ℝ :=
    fun h =>
      (2 * Real.pi) ^ 3 * M (t + h * u)
        +
      ‖T h - E‖

  have hhZero :
      Tendsto
        (fun h : ℝ => h)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds

  have hArg :
      Tendsto
        (fun h : ℝ => t + h * u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 t) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (hhZero.mul_const u)

  have hMassBase :
      Tendsto M (𝓝 t) (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceThirdMass_tendsto_zero
        hν U₀ hA hU₀ ht htR i

  have hMass :
      Tendsto
        (fun h : ℝ => M (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) :=
    hMassBase.comp hArg

  have hCoeff :
      Tendsto
        (fun _h : ℝ => ((2 * Real.pi) ^ 3 : ℝ))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 ((2 * Real.pi) ^ 3)) :=
    tendsto_const_nhds

  have hMovingUpperTend :
      Tendsto
        (fun h : ℝ =>
          (2 * Real.pi) ^ 3 * M (t + h * u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [mul_zero] using hCoeff.mul hMass

  have hLagFull :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    simpa only [zero_mul] using
      hhZero.mul_const (1 - u)

  have hOneMinus :
      0 ≤ 1 - u := by
    linarith [hu.2]

  have hLagMaps :
      MapsTo
        (fun h : ℝ => h * (1 - u))
        (Set.Ici (0 : ℝ))
        (Set.Ici (0 : ℝ)) := by
    intro h hh
    exact mul_nonneg hh hOneMinus

  have hLag :
      Tendsto
        (fun h : ℝ => h * (1 - u))
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝[Set.Ici (0 : ℝ)] 0) := by
    exact
      tendsto_inf.2
        ⟨hLagFull,
          tendsto_principal.2 <|
            mem_inf_of_right <|
              mem_principal.2 hLagMaps⟩

  have hFrozen :
      Tendsto
        T
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    have h0 :=
      (tendsto_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR.le i a b c x).comp hLag
    dsimp only [T, E, W]
    exact h0

  have hFrozenDiff :
      Tendsto
        (fun h : ℝ => ‖T h - E‖)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    have hEConst :
        Tendsto
          (fun _h : ℝ => E)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 E) :=
      tendsto_const_nhds
    simpa using (hFrozen.sub hEConst).norm

  have hgZero :
      Tendsto
        g
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 0) := by
    dsimp only [g]
    simpa only [zero_add] using
      hMovingUpperTend.add hFrozenDiff

  have hInterior :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 t :=
    Ioo_mem_nhds ht htR

  have hArgInterior :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        t + h * u ∈
          Set.Ioo
            (0 : ℝ)
            (h3FinHeatLerayRestartRadius ν A) :=
    hArg.eventually hInterior

  have hUpper :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ‖h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
              ν t h W i a b c x u
            -
          E‖
          ≤
        g h := by
    filter_upwards
      [self_mem_nhdsWithin, hArgInterior]
      with h hh hri

    by_cases hh0 : h = 0

    · subst h
      dsimp only [g, T, E, M]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
      ]
      simp only [zero_mul, add_zero, one_mul, norm_zero, zero_add]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
          hν U₀ hA hU₀ ht htR.le i a b c x
      ]
      dsimp only [W]
      simp

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      have hu1 :
          0 < 1 - u := by
        linarith [hu.2]

      have hlag :
          0 < h * (1 - u) :=
        mul_pos hhpos hu1

      let R0 : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a b c x

      have hFreshEq :
          h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
              ν t h W i a b c x u
            =
          R0 := by
        dsimp only [R0]
        exact
          h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
            ν t h W i a b c x u

      have hMove :
          ‖R0 - T h‖
            ≤
          (2 * Real.pi) ^ 3 *
            M (t + h * u) := by
        dsimp only [R0, T, M, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_sub_le_differenceThirdMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a b c x

      rw [hFreshEq]

      have hSplit :
          R0 - E
            =
          (R0 - T h) + (T h - E) := by
        abel

      rw [hSplit]

      calc
        ‖(R0 - T h) + (T h - E)‖
            ≤
          ‖R0 - T h‖ + ‖T h - E‖ :=
          norm_add_le _ _
        _ ≤
          (2 * Real.pi) ^ 3 *
              M (t + h * u)
            +
          ‖T h - E‖ :=
          add_le_add hMove (le_refl _)
        _ = g h := by
          rfl

  have hNonneg :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        0 ≤
          ‖h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
              ν t h W i a b c x u
            -
          E‖ :=
    Eventually.of_forall
      (fun h => norm_nonneg _)

  have hToE :
      Tendsto
        (h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t · W i a b c x u)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 E) := by
    exact
      (tendsto_iff_norm_sub_tendsto_zero).2
        (squeeze_zero'
          hNonneg
          hUpper
          hgZero)

  dsimp only [E, W] at hToE
  exact hToE

end

end Euclidean
end Bridge
end PrimeTensor
