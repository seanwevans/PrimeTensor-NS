import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedFrozenFrequencyIntegral

/-!
# Selected quarter-Hölder forcing: frozen half-tail Fubini closure

`Forcing.SelectedFrozenFrequencyIntegral` controls the frozen terminal
half-tail after integrating first in source time and then in frequency.
The second-Duhamel formula naturally presents the same nonnegative scalar
profile in the opposite order.

This file closes that purely measure-theoretic gap.  The key step is product
integrability on

    H3FourierPoint3 × (t/2,t).

For each fixed frequency the source-time section is continuous.  The outer
integrability required by `integrable_prod_iff` is obtained from the already
proved fixed-frequency primitive bound and the terminal forcing `L¹` mass.
Fubini then swaps the two integrals, yielding the frozen half-tail budget in
the time-outer / frequency-inner order needed downstream.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedFrozenFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The nonnegative frozen half-tail second-moment kernel is integrable on the
frequency/source-time product space. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun p : H3FourierPoint3 × ℝ =>
        (‖p.1‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i p.1‖)
      ((volume : Measure H3FourierPoint3).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence (W t) (W t) i

  let f : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (‖p.1‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
        ‖N p.1‖

  let cInv : ℝ := ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hhalf : t / 2 ≤ t := by
    linarith

  have hc : 0 < (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    exact inv_nonneg.mpr hc.le

  have hN : Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hHeatFactorContinuous :
      Continuous
        (fun p : H3FourierPoint3 × ℝ =>
          ‖p.1‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) := by
    unfold h3HeatFourierSymbol
    fun_prop

  have hJoint :
      AEStronglyMeasurable
        f
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    have hHeatMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            ‖p.1‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - p.2) p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      hHeatFactorContinuous.aestronglyMeasurable

    have hNMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ => ‖N p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      hN.norm.aestronglyMeasurable.comp_fst

    dsimp only [f]
    exact hHeatMeas.mul hNMeas

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 => cInv * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hN.norm.const_mul cInv

  refine (integrable_prod_iff hJoint).2 ?_
  constructor
  · exact Filter.Eventually.of_forall fun ξ => by
      have hSecCont :
          Continuous (fun s : ℝ => f (ξ, s)) := by
        dsimp only [f]
        unfold h3HeatFourierSymbol
        fun_prop

      have hSecInterval :
          IntervalIntegrable (fun s : ℝ => f (ξ, s)) volume (t / 2) t :=
        hSecCont.intervalIntegrable (t / 2) t

      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hSecInterval
      rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hSecInterval
      exact hSecInterval

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ∫ s : ℝ, ‖f (ξ, s)‖
              ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          (volume : Measure H3FourierPoint3) :=
      hJoint.norm.integral_prod_right'

    refine hMajorantInt.mono' hOuterMeas ?_
    filter_upwards with ξ

    have hInnerEq :
        (∫ s : ℝ, ‖f (ξ, s)‖
            ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          =
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae
      filter_upwards with s
      dsimp only [f]
      have hf0 :
          0 ≤
            (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) * ‖N ξ‖ := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      rw [norm_mul]
      ring

    have hBound :
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤ cInv * ‖N ξ‖ := by
      dsimp only [cInv, N, W]
      exact
        h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_le
          hν U₀ hA hU₀ ht i ξ

    have hInnerNonneg :
        0 ≤
          ∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      exact intervalIntegral.integral_nonneg hhalf (fun _ _ => by positivity)

    rw [hInnerEq, Real.norm_eq_abs, abs_of_nonneg hInnerNonneg]
    exact hBound

/-- Fubini swaps the frozen half-tail from frequency-outer/source-time-inner
order to source-time-outer/frequency-inner order. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_integral_swap
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      =
    ∫ s in (t / 2)..t,
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : H3FourierPoint3 → ℝ → ℝ :=
    fun ξ s =>
      (‖ξ‖ ^ 2 * ‖h3HeatFourierSymbol ν (t - s) ξ‖) *
        ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖

  have hhalf : t / 2 ≤ t := by
    linarith

  have hInt :
      Integrable (Function.uncurry f)
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    dsimp only [Function.uncurry, f, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_fubini_integrable
        hν U₀ hA hU₀ ht i

  have hSwap :=
    integral_integral_swap
      (μ := (volume : Measure H3FourierPoint3))
      (ν := ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ ξ : H3FourierPoint3,
          ∫ s in Set.Ioo (t / 2) t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ *
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ s in Set.Ioo (t / 2) t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
    simpa only [f, norm_mul, mul_assoc] using hSwap

  calc
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s in Set.Ioo (t / 2) t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [intervalIntegral.integral_of_le hhalf]
          rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ s in Set.Ioo (t / 2) t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ :=
      hSwapExpanded
    _ =
      ∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
          symm
          rw [intervalIntegral.integral_of_le hhalf]
          rw [← restrict_Ioo_eq_restrict_Ioc]

/-- The frozen terminal contribution on the half-tail is bounded in the
source-time-outer/frequency-inner order used by the second-Duhamel formula. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_time_frequencyIntegral_le_selectedRestart
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hSwap :=
    h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_integral_swap
      hν U₀ hA hU₀ ht i

  have hFreq :=
    h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_frequency_timeIntegral_le_selectedRestart
      hν U₀ hA hU₀ ht i

  calc
    (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖ := by
          symm
          simpa only [W] using hSwap
    _ ≤
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
      simpa only [W] using hFreq

end

end Euclidean
end Bridge
end PrimeTensor
