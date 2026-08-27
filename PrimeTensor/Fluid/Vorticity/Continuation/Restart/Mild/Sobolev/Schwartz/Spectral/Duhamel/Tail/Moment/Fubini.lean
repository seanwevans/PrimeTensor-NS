import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.KernelMeasurable

/-!
# Selected terminal-tail second-moment Fubini closure

The selected terminal-tail second-moment density is now jointly measurable on

    ℝ × H3FourierPoint3,

and the endpoint-quarter branch already proves that its time-outer /
frequency-inner integral on `(t/2,t)` is finite.

This file closes the purely measure-theoretic bridge:

* the actual variable-state terminal-tail density is integrable on the
  restricted time-frequency product measure;
* Fubini swaps source time and Fourier frequency;
* the resulting frequency-outer/source-time-inner integral is controlled by
  the canonical selected second-moment budget.

This is the form needed to construct the time-integrated raw Fourier tail
amplitude and prove that it carries two integrable Fourier moments.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailSecondMomentFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected terminal-tail second-moment density is genuinely integrable
on the restricted source-time/Fourier-frequency product space. -/
theorem h3SelectedDuhamelTailSecondMomentKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailSecondMomentKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let f : ℝ × H3FourierPoint3 → ℝ :=
    h3SelectedDuhamelTailSecondMomentKernel
      ν A t hν U₀ hA hU₀ i

  let P : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondMomentProfile ν t W i

  have hJoint :
      AEStronglyMeasurable
        f
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) := by
    dsimp only [f]
    exact
      (measurable_h3SelectedDuhamelTailSecondMomentKernel
        hν U₀ hA hU₀ i).aestronglyMeasurable

  have hhalf : t / 2 ≤ t := by
    linarith

  have hProfileInterval :
      IntervalIntegrable
        P
        volume
        (t / 2)
        t := by
    dsimp only [P, W]
    exact
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  have hProfileInt :
      Integrable
        P
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hProfileInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hProfileInterval
    exact hProfileInterval

  have hOuterEq :
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3,
          ‖f (s, ξ)‖)
        =
      P := by
    funext s
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp only [
      f,
      P,
      h3SelectedDuhamelTailSecondMomentKernel,
      h3NonlinearForcingHeatSecondMomentProfile
    ]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs

    have hτ : 0 < t - s := by
      exact sub_pos.mpr hs.2

    have hMoment :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W s) (W s) i 2 (by norm_num)

    dsimp only [f]
    unfold h3SelectedDuhamelTailSecondMomentKernel

    simpa only [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative
    ] using hMoment

  · rw [hOuterEq]
    exact hProfileInt

/-- Fubini swaps the selected terminal-tail second-moment density from
source-time-outer/frequency-inner order to
frequency-outer/source-time-inner order. -/
theorem h3SelectedDuhamelTailSecondMomentKernel_integral_swap
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ∫ ξ : H3FourierPoint3,
      ∫ s in (t / 2)..t,
        h3SelectedDuhamelTailSecondMomentKernel
          ν A t hν U₀ hA hU₀ i (s, ξ) := by
  let f : ℝ → H3FourierPoint3 → ℝ :=
    fun s ξ =>
      h3SelectedDuhamelTailSecondMomentKernel
        ν A t hν U₀ hA hU₀ i (s, ξ)

  have hhalf : t / 2 ≤ t := by
    linarith

  have hInt :
      Integrable
        (Function.uncurry f)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) := by
    dsimp only [Function.uncurry, f]
    exact
      h3SelectedDuhamelTailSecondMomentKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hSwap :=
    integral_integral_swap
      (μ := ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
      (ν := (volume : Measure H3FourierPoint3))
      (f := f)
      hInt

  have hSwapExpanded :
      (∫ s in Set.Ioo (t / 2) t,
          ∫ ξ : H3FourierPoint3,
            h3SelectedDuhamelTailSecondMomentKernel
              ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s in Set.Ioo (t / 2) t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
    simpa only [f] using hSwap

  calc
    (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ s in Set.Ioo (t / 2) t,
        ∫ ξ : H3FourierPoint3,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
          rw [intervalIntegral.integral_of_le hhalf]
          rw [← restrict_Ioo_eq_restrict_Ioc]
    _ =
      ∫ ξ : H3FourierPoint3,
        ∫ s in Set.Ioo (t / 2) t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
      hSwapExpanded
    _ =
      ∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
          apply integral_congr_ae
          filter_upwards with ξ
          symm
          rw [intervalIntegral.integral_of_le hhalf]
          rw [← restrict_Ioo_eq_restrict_Ioc]

/-- Frequency-outer/source-time-inner form of the selected terminal-tail second
Fourier-moment budget. -/
theorem h3SelectedDuhamelTailSecondMomentKernel_frequencyTimeIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  have hSwap :=
    h3SelectedDuhamelTailSecondMomentKernel_integral_swap
      hν U₀ hA hU₀ ht htR i

  have hTimeBudget :=
    h3RawFinLerayOuterProductDivergenceHeat_selectedDuhamelTail_secondMoment_timeFrequencyIntegral_le
      hν U₀ hA hU₀ ht htR i

  calc
    (∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ))
        =
      ∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
          symm
          exact hSwap
    _ =
      ∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s)
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s)
                i ξ‖ := by
          apply intervalIntegral.integral_congr
          intro s hs
          apply integral_congr_ae
          filter_upwards with ξ
          rfl
    _ ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t :=
        hTimeBudget

end
end Euclidean
end Bridge
end PrimeTensor
