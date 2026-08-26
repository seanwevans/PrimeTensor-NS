import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Majorant

/-!
# Integrated quarter-power bound for the old Duhamel history

`Quarter.Duhamel.History.Majorant` reduced the selected positive-lag kernel
increment to the integrable scalar singularity

    C * h^(1/4) * (t-s)^(-3/4).

This file performs the Bochner interval-integral step on the old history
`0..t`.  The endpoint `s=t` is defined to be zero, exactly as for the
retarded Duhamel integrand itself, while every strict history time uses the
selected-restart kernel theorem.

The resulting old-history contribution is bounded by

    4 C * h^(1/4) * t^(1/4).

No Duhamel restart algebra is used here; the next rung can identify this
integral with the old-history part of the actual Duhamel increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- The selected positive-lag kernel increment on the old history.  The
terminal endpoint is set to zero so no positive-lag witness is required. -/
noncomputable def h3DuhamelQuarterSelectedHistoryKernelDifference
    (ν : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (A : ℝ)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (t : ℝ)
    (h : NNReal)
    (s : ℝ) :
    H3SpectralFinVectorState :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  if hs : s < t then
    h3SpectralVelocityHeatApplyNN ν hν.le h
        (h3SpectralFinHeatLerayVelocityApply
          ν (t - s) hν (sub_pos.mpr hs) (W s) (W s)) -
      h3SpectralFinHeatLerayVelocityApply
        ν (t - s) hν (sub_pos.mpr hs) (W s) (W s)
  else
    0

/-- Pointwise selected-history kernel difference is controlled by the
normalized `-3/4` time majorant. -/
theorem norm_h3DuhamelQuarterSelectedHistoryKernelDifference_le
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (h : NNReal)
    (hs0t : s ∈ Set.Ioc (0 : ℝ) t) :
    ‖h3DuhamelQuarterSelectedHistoryKernelDifference
        ν hν U₀ A hA hU₀ t h s‖
      ≤
    h3DuhamelQuarterHistoryTimeMajorant
      ν t (h : ℝ) (2 * A) (2 * A) s := by
  by_cases hst : s < t
  · unfold h3DuhamelQuarterSelectedHistoryKernelDifference
    simp only [dif_pos hst]
    calc
      ‖h3SpectralVelocityHeatApplyNN ν hν.le h
            (h3SpectralFinHeatLerayVelocityApply
              ν (t - s) hν (sub_pos.mpr hst)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s)) -
          h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν (sub_pos.mpr hst)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s)‖
          ≤
        h3DuhamelQuarterHistoryKernelMajorant
          ν (t - s) (h : ℝ) (2 * A) (2 * A) := by
            simpa only using
              (norm_h3SpectralVelocityHeatApplyNN_selectedRestart_heatLeray_history_sub_le_quarter
                hν U₀ hA hU₀ hst h)
      _ =
        h3DuhamelQuarterHistoryTimeMajorant
          ν t (h : ℝ) (2 * A) (2 * A) s := by
            exact
              h3DuhamelQuarterHistoryKernelMajorant_eq_timeMajorant
                hν hst h.property
  · have hst_eq : s = t := by
      exact le_antisymm hs0t.2 (le_of_not_gt hst)
    subst s
    unfold h3DuhamelQuarterSelectedHistoryKernelDifference
    have htt : ¬ t < t := lt_irrefl t
    simp only [dif_neg htt, norm_zero]
    unfold h3DuhamelQuarterHistoryTimeMajorant
    simp

/-- The old-history selected kernel increment is bounded by the exact
integral of the normalized quarter majorant. -/
theorem norm_h3DuhamelQuarterSelectedHistoryKernelDifference_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (h : NNReal) :
    ‖∫ s in (0 : ℝ)..t,
        h3DuhamelQuarterSelectedHistoryKernelDifference
          ν hν U₀ A hA hU₀ t h s‖
      ≤
    4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
      (h : ℝ) ^ ((1 : ℝ) / 4) *
      t ^ ((1 : ℝ) / 4) := by
  have hMajorantInt :
      IntervalIntegrable
        (h3DuhamelQuarterHistoryTimeMajorant
          ν t (h : ℝ) (2 * A) (2 * A))
        volume
        0
        t :=
    h3DuhamelQuarterHistoryTimeMajorant_intervalIntegrable

  have hPointwise :
      ∀ᵐ s : ℝ ∂volume,
        s ∈ Set.Ioc (0 : ℝ) t →
          ‖h3DuhamelQuarterSelectedHistoryKernelDifference
              ν hν U₀ A hA hU₀ t h s‖
            ≤
          h3DuhamelQuarterHistoryTimeMajorant
            ν t (h : ℝ) (2 * A) (2 * A) s := by
    filter_upwards with s
    intro hs
    exact
      norm_h3DuhamelQuarterSelectedHistoryKernelDifference_le
        hν U₀ hA hU₀ h hs

  have hBound :
      ‖∫ s in (0 : ℝ)..t,
          h3DuhamelQuarterSelectedHistoryKernelDifference
            ν hν U₀ A hA hU₀ t h s‖
        ≤
      ∫ s in (0 : ℝ)..t,
        h3DuhamelQuarterHistoryTimeMajorant
          ν t (h : ℝ) (2 * A) (2 * A) s := by
    exact
      intervalIntegral.norm_integral_le_of_norm_le
        ht
        hPointwise
        hMajorantInt

  exact
    hBound.trans_eq
      (h3DuhamelQuarterHistoryTimeMajorant_integral
        (ν := ν)
        (t := t)
        (h := (h : ℝ))
        (MU := 2 * A)
        (MV := 2 * A)
        ht)

end

end Euclidean
end Bridge
end PrimeTensor
