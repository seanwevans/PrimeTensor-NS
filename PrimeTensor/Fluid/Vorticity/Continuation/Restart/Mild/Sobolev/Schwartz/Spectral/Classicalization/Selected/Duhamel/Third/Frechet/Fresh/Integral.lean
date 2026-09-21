import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.Fresh.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spectral.Fin.Heat.Leray.Duhamel.Raw.Fourier.Joint.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Classicalization: third-Fréchet fresh-tail fixed-domain integral

The rescaled third-Fréchet fresh integrand now converges pointwise on
`u ∈ (0,1)` to the instantaneous selected forcing third-coordinate derivative.

This file supplies the fixed-domain dominated-convergence step.

Put

    M(r) = ∫ |ξ|³ |N̂(W(r),W(r)) - N̂(W(t),W(t))|.

The selected forcing cubic-difference theorem gives `M(r) → 0`.  Hence near
`t`, `M(r) < 1`.  For sufficiently small nonnegative `h`, every
`t + h u`, `u ∈ [0,1]`, stays in that neighborhood and in the restart
interval.

The moving-state contribution is then bounded by `(2π)^3`.  The frozen-state
positive-lag third coordinate is bounded by `(2π)^3` times the unheated cubic
Fourier mass.  These give a constant dominator on the unit interval.

Joint measurability of the selected retarded Fourier kernel supplies
measurability of every rescaled physical slice by integrating out frequency.

Therefore

    ∫₀¹ freshThirdFrechetRescaled(h,u) du
      ⟶
    D³N(W(t),W(t))(x)[e_a,e_b,e_c].
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetFreshIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a selected positive time, positive heat lag cannot increase the
pointwise ordered third-coordinate reconstruction beyond `(2π)^3` times the
unheated radial cubic Fourier mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_le_unheatedThirdMoment
    {ν A t τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hτ : 0 < τ)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
        ν τ (W t) (W t) i a b c x‖
      ≤
    (2 * Real.pi) ^ 3 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let raw : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let heated : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ (W t) (W t) i

  let K : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
      ν τ (W t) (W t) i a b c x

  have hRaw3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖raw ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hHeat3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖heated ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [heated]
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W t) (W t) i 3 (by norm_num)

  have hHeatPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖heated ξ‖
          ≤
        ‖ξ‖ ^ 3 * ‖raw ξ‖ := by
    intro ξ
    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ
    dsimp only [heated, raw]
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_left
        (by
          calc
            ‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖
                ≤
              1 *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖ :=
              mul_le_mul_of_nonneg_right hHeat (norm_nonneg _)
            _ =
              ‖h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖ := by
              rw [one_mul])
        (by positivity)

  have hHeatMassLe :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖heated ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖raw ξ‖ := by
    exact
      integral_mono_ae
        hHeat3
        hRaw3
        (Filter.Eventually.of_forall hHeatPoint)

  have hK :
      Integrable K
        (volume : Measure H3FourierPoint3) := by
    dsimp only [K]
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-x)]

    have hAmpMeas :
        AEStronglyMeasurable
          (h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν τ (W t) (W t) i a b c)
          (volume : Measure H3FourierPoint3) := by
      unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
      exact
        (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
              (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                ν τ (W t) (W t) i)))

    have hMajor :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            (2 * Real.pi) ^ 3 *
              (‖ξ‖ ^ 3 * ‖heated ξ‖))
          (volume : Measure H3FourierPoint3) :=
      hHeat3.const_mul ((2 * Real.pi) ^ 3)

    refine hMajor.mono' hAmpMeas ?_
    filter_upwards with ξ
    dsimp only [heated]
    exact
      norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
        ν τ (W t) (W t) i a b c ξ

  rw [
    h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_eq_integral_kernel
  ]

  calc
    ‖∫ ξ : H3FourierPoint3, K ξ‖
        ≤
      ∫ ξ : H3FourierPoint3, ‖K ξ‖ :=
        norm_integral_le_integral_norm _
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) ^ 3 *
          (‖ξ‖ ^ 3 * ‖heated ξ‖) := by
        refine integral_mono_ae hK.norm ?_ ?_
        · exact
            (hHeat3.const_mul ((2 * Real.pi) ^ 3))
        · filter_upwards with ξ
          dsimp only [K]
          unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateFourierKernel
          simp only [Circle.norm_smul]
          exact
            norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude_le_thirdMoment
              ν τ (W t) (W t) i a b c ξ
    _ =
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖heated ξ‖) := by
        rw [integral_const_mul]
    _ ≤
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖raw ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            hHeatMassLe
            (by positivity)
    _ =
      (2 * Real.pi) ^ 3 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖) := by
        rfl

/-- For every fixed increment, the rescaled physical third-coordinate fresh
integrand is a.e. strongly measurable on the unit interval. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_aestronglyMeasurable
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    AEStronglyMeasurable
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t h W i a b c x u)
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μu : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let K : ℝ × H3FourierPoint3 → ℂ :=
    fun p =>
      phase p.2 *
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
          ν (h * (1 - p.1))
          (W (t + h * p.1))
          (W (t + h * p.1))
          i a b c p.2

  let Wh : ℝ → H3SpectralFinVectorState :=
    fun u => W (t + h * u)

  have hW :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hAffine :
      Continuous
        (fun u : ℝ => t + h * u) := by
    fun_prop

  have hWh :
      Continuous Wh := by
    dsimp only [Wh]
    exact hW.comp hAffine

  have hRawJointWh :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence
            (Wh p.1) (Wh p.1) i p.2) := by
    exact
      measurable_h3RawFinLerayOuterProductDivergence_continuousPaths_joint
        Wh Wh hWh hWh i

  have hRawJoint :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergence
            (W (t + h * p.1))
            (W (t + h * p.1))
            i p.2) := by
    simpa only [Wh] using hRawJointWh

  have hHeat :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (h * (1 - p.1)) p.2) := by
    unfold h3HeatFourierSymbol
    fun_prop

  have ha :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol a p.2) :=
    (h3FourierDerivativeSymbol_continuous a).measurable.comp measurable_snd

  have hb :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol b p.2) :=
    (h3FourierDerivativeSymbol_continuous b).measurable.comp measurable_snd

  have hc :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierDerivativeSymbol c p.2) :=
    (h3FourierDerivativeSymbol_continuous c).measurable.comp measurable_snd

  have hPhaseContinuous :
      Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hPhase :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          phase p.2) :=
    hPhaseContinuous.measurable.comp measurable_snd

  have hAmp :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
            ν (h * (1 - p.1))
            (W (t + h * p.1))
            (W (t + h * p.1))
            i a b c p.2) := by
    unfold h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateAmplitude
    exact
      ha.mul
        (hb.mul
          (hc.mul
            (hHeat.mul hRawJoint)))

  have hK :
      AEStronglyMeasurable
        K
        (μu.prod (volume : Measure H3FourierPoint3)) := by
    have hKMeas :
        Measurable K := by
      dsimp only [K]
      exact hPhase.mul hAmp
    exact
      hKMeas.aestronglyMeasurable

  have hOuter :
      AEStronglyMeasurable
        (fun u : ℝ =>
          ∫ ξ : H3FourierPoint3, K (u, ξ))
        μu :=
    hK.integral_prod_right'

  have hEq :
      (fun u : ℝ =>
        ∫ ξ : H3FourierPoint3, K (u, ξ))
        =
      (fun u : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
          ν t h W i a b c x u) := by
    funext u
    rw [
      h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
    ]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
    rw [Real.fourierInv_eq']
    dsimp only [K, phase]
    simp only [smul_eq_mul]

  rw [hEq] at hOuter
  exact hOuter

/-- The selected rescaled third-Fréchet fresh integral converges from the right
to the instantaneous forcing third-coordinate derivative. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
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

  let J : ℝ :=
    (2 * Real.pi) ^ 3 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖)

  let B : ℝ :=
    (2 * Real.pi) ^ 3 + J + ‖E‖

  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) 1)

  let F : ℝ → ℝ → ℂ :=
    fun h u =>
      h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
        ν t h W i a b c x u

  let bound : ℝ → ℝ :=
    fun _u => B

  have hMassBase :
      Tendsto M (𝓝 t) (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceThirdMass_tendsto_zero
        hν U₀ hA hU₀ ht htR i

  have hMassNhds :
      M ⁻¹' Set.Iio (1 : ℝ) ∈ 𝓝 t := by
    exact
      hMassBase
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

  rcases Metric.mem_nhds_iff.1 hMassNhds with
    ⟨ε, hε, hεball⟩

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let δ : ℝ :=
    min ε (R - t)

  have hRt :
      0 < R - t := by
    dsimp only [R]
    linarith

  have hδ :
      0 < δ := by
    dsimp only [δ]
    exact lt_min hε hRt

  have hSmall :
      Set.Iio δ ∈ (𝓝[Set.Ici (0 : ℝ)] 0) := by
    exact
      mem_inf_of_left
        (Iio_mem_nhds hδ)

  have hCoeffNonneg :
      0 ≤ (2 * Real.pi) ^ 3 := by
    positivity

  have hBnonneg :
      0 ≤ B := by
    dsimp only [B]
    positivity

  have hFMeas :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F h)
          μ := by
    exact Filter.Eventually.of_forall fun h => by
      dsimp only [F, μ, W]
      exact
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_aestronglyMeasurable
          hν U₀ hA hU₀ i a b c x

  have hBoundAE :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ u : ℝ ∂μ,
          ‖F h u‖ ≤ bound u := by
    filter_upwards
      [self_mem_nhdsWithin, hSmall]
      with h hh hhd

    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu

    have huu :
        h * u ≤ h := by
      have hu1 : u ≤ 1 := hu.2.le
      calc
        h * u ≤ h * 1 :=
          mul_le_mul_of_nonneg_left hu1 hh
        _ = h := by ring

    have hhu0 :
        0 ≤ h * u :=
      mul_nonneg hh hu.1.le

    have hδeps :
        δ ≤ ε := by
      dsimp only [δ]
      exact min_le_left _ _

    have hδR :
        δ ≤ R - t := by
      dsimp only [δ]
      exact min_le_right _ _

    have hhuε :
        h * u < ε := by
      calc
        h * u ≤ h := huu
        _ < δ := hhd
        _ ≤ ε := hδeps

    have hdist :
        dist (t + h * u) t < ε := by
      rw [Real.dist_eq]
      have hsub :
          t + h * u - t = h * u := by
        ring
      rw [hsub, abs_of_nonneg hhu0]
      exact hhuε

    have hMlt :
        M (t + h * u) < 1 :=
      hεball hdist

    have hri :
        t + h * u ∈ Set.Ioo (0 : ℝ) R := by
      constructor
      · linarith
      · have hhuR :
            h * u < R - t := by
          calc
            h * u ≤ h := huu
            _ < δ := hhd
            _ ≤ R - t := hδR
        linarith

    by_cases hh0 : h = 0

    · subst h
      dsimp only [F, bound, B]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
      ]
      simp only [zero_mul, add_zero]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
          hν U₀ hA hU₀ ht htR.le i a b c x
      ]
      dsimp only [E]
      have hLeft :
          0 ≤ (2 * Real.pi) ^ 3 + J := by
        positivity
      linarith [norm_nonneg
        (iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c)
          ])]

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      have hu1 :
          0 < 1 - u := by
        linarith [hu.2]

      have hlag :
          0 < h * (1 - u) :=
        mul_pos hhpos hu1

      let Q : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a b c x

      let T : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative
          ν (h * (1 - u))
          (W t) (W t)
          i a b c x

      have hFEq :
          F h u = Q := by
        dsimp only [F, Q]
        exact
          h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_eq_thirdCoordinateRepresentative
            ν t h W i a b c x u

      have hMove :
          ‖Q - T‖
            ≤
          (2 * Real.pi) ^ 3 *
            M (t + h * u) := by
        dsimp only [Q, T, M, W, R] at hri ⊢
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_sub_le_differenceThirdMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a b c x

      have hMoveOne :
          ‖Q - T‖
            ≤
          (2 * Real.pi) ^ 3 := by
        calc
          ‖Q - T‖
              ≤
            (2 * Real.pi) ^ 3 *
              M (t + h * u) :=
            hMove
          _ ≤
            (2 * Real.pi) ^ 3 * 1 := by
              exact
                mul_le_mul_of_nonneg_left
                  hMlt.le
                  hCoeffNonneg
          _ = (2 * Real.pi) ^ 3 := by
              ring

      have hFixed :
          ‖T‖ ≤ J := by
        dsimp only [T, J, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatThirdCoordinateRepresentative_selectedRestart_le_unheatedThirdMoment
            hν U₀ hA hU₀ ht htR.le hlag i a b c x

      rw [hFEq]
      dsimp only [bound, B]

      calc
        ‖Q‖
            ≤
          ‖Q - T‖ + ‖T‖ := by
            have hAlg :
                Q = (Q - T) + T := by
              abel
            calc
              ‖Q‖ = ‖(Q - T) + T‖ :=
                congrArg norm hAlg
              _ ≤ ‖Q - T‖ + ‖T‖ :=
                norm_add_le _ _
        _ ≤
          (2 * Real.pi) ^ 3 + J :=
          add_le_add hMoveOne hFixed
        _ ≤
          (2 * Real.pi) ^ 3 + J + ‖E‖ := by
          exact le_add_of_nonneg_right (norm_nonneg E)

  have hBoundInt :
      Integrable bound μ := by
    dsimp only [bound, μ]
    change
      IntegrableOn
        (fun _u : ℝ => B)
        (Set.Ioo (0 : ℝ) 1)
        volume
    rw [
      ← intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ]
    exact intervalIntegrable_const

  have hLim :
      ∀ᵐ u : ℝ ∂μ,
        Tendsto
          (fun h : ℝ => F h u)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 E) := by
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    dsimp only [F, E, W]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR hu i a b c x

  have hMain :
      Tendsto
        (fun h : ℝ =>
          ∫ u : ℝ, F h u ∂μ)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝
          (∫ _u : ℝ, E ∂μ)) := by
    exact
      tendsto_integral_filter_of_dominated_convergence
        (μ := μ)
        (l := (𝓝[Set.Ici (0 : ℝ)] 0))
        (F := F)
        (f := fun _u : ℝ => E)
        (bound := bound)
        hFMeas
        hBoundAE
        hBoundInt
        hLim

  have hPathEq :
      (fun h : ℝ =>
        ∫ u : ℝ, F h u ∂μ)
        =
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshThirdFrechetRescaledIntegrand
            ν t h W i a b c x u) := by
    funext h
    dsimp only [F, μ]
    rw [
      intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hLimitEq :
      (∫ _u : ℝ, E ∂μ) = E := by
    dsimp only [μ]
    have hConst :
        (∫ u in (0 : ℝ)..1, E) = E := by
      simp
    rw [
      intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ] at hConst
    rw [← restrict_Ioo_eq_restrict_Ioc] at hConst
    exact hConst

  rw [hPathEq, hLimitEq] at hMain
  dsimp only [E, W] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
