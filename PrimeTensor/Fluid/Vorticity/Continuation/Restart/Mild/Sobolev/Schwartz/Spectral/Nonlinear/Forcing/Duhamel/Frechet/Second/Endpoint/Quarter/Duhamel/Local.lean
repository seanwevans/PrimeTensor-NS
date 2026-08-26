import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Increment

/-!
# Local terminal quarter-Hölder control of the selected Duhamel path

The forward increment estimate from `Quarter.Duhamel.Increment` has a history
coefficient depending on the positive base time `s` through `s^(1/4)`.
On a fixed terminal interval `(a,t)`, that factor is bounded by `t^(1/4)`.
This file packages that observation into a single coefficient depending only
on the terminal time and proves the terminal quarter-Hölder estimate needed by
the endpoint predicate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- Uniform coefficient for the selected Duhamel path on a terminal interval
ending at `t`. -/
noncomputable def h3DuhamelQuarterSelectedRestartLocalCoefficient
    (ν A t : ℝ) : ℝ :=
  4 * h3DuhamelQuarterHistoryPowerCoefficient
        ν (2 * A) (2 * A) *
      t ^ ((1 : ℝ) / 4) +
    h3DuhamelQuarterSelectedRestartCoefficient ν A

/-- The local selected-Duhamel coefficient is nonnegative at nonnegative
viscosity, radius, and terminal time. -/
theorem h3DuhamelQuarterSelectedRestartLocalCoefficient_nonneg
    {ν A t : ℝ}
    (hν : 0 ≤ ν)
    (hA : 0 ≤ A)
    (ht : 0 ≤ t) :
    0 ≤ h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t := by
  have h2A : 0 ≤ 2 * A := by positivity
  have hHistory :
      0 ≤ h3DuhamelQuarterHistoryPowerCoefficient
        ν (2 * A) (2 * A) :=
    h3DuhamelQuarterHistoryPowerCoefficient_nonneg hν h2A h2A
  have htPow : 0 ≤ t ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg ht _
  have hRestart :
      0 ≤ h3DuhamelQuarterSelectedRestartCoefficient ν A :=
    h3DuhamelQuarterSelectedRestartCoefficient_nonneg ν hA
  unfold h3DuhamelQuarterSelectedRestartLocalCoefficient
  positivity

/-- On any positive terminal interval `(a,t)`, the selected Duhamel path has a
single terminal quarter-Hölder coefficient independent of the source time
`s`. -/
theorem norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_sub_le_quarter_on
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ∀ s ∈ Set.Ioo a t,
      ‖h3SpectralFinHeatLerayDuhamel ν s hν W W -
          h3SpectralFinHeatLerayDuhamel ν t hν W W‖
        ≤
      h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t *
        (t - s) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  intro s hs

  have hs0 : 0 < s := lt_trans ha hs.1
  have ht0 : 0 ≤ t := (lt_trans ha hat).le
  have hlag : 0 < t - s := sub_pos.mpr hs.2
  have hlag0 : 0 ≤ t - s := hlag.le

  let h : NNReal := ⟨t - s, hlag0⟩

  have hh : 0 < h := by
    exact_mod_cast hlag

  have hhR :
      (h : ℝ) ≤ h3FinHeatLerayRestartRadius ν A := by
    change t - s ≤ h3FinHeatLerayRestartRadius ν A
    calc
      t - s ≤ t := sub_le_self t hs0.le
      _ ≤ h3FinHeatLerayRestartRadius ν A := htR

  have hInc0 :=
    norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_add_time_sub_le_quarter
      hν U₀ hA hU₀ hs0 h hh hhR

  have hInc :
      ‖h3SpectralFinHeatLerayDuhamel ν (s + (h : ℝ)) hν W W -
          h3SpectralFinHeatLerayDuhamel ν s hν W W‖
        ≤
      (4 * h3DuhamelQuarterHistoryPowerCoefficient
            ν (2 * A) (2 * A) *
          s ^ ((1 : ℝ) / 4) +
        h3DuhamelQuarterSelectedRestartCoefficient ν A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
    simpa only [W] using hInc0

  have hst : s + (h : ℝ) = t := by
    change s + (t - s) = t
    ring

  have h2A : 0 ≤ 2 * A := by positivity

  have hHistoryPower :
      0 ≤ h3DuhamelQuarterHistoryPowerCoefficient
        ν (2 * A) (2 * A) :=
    h3DuhamelQuarterHistoryPowerCoefficient_nonneg
      hν.le h2A h2A

  have hHistoryCoeff :
      0 ≤ 4 * h3DuhamelQuarterHistoryPowerCoefficient
        ν (2 * A) (2 * A) := by
    positivity

  have hTimePow :
      s ^ ((1 : ℝ) / 4) ≤ t ^ ((1 : ℝ) / 4) := by
    exact Real.rpow_le_rpow hs0.le hs.2.le (by norm_num)

  have hCoeff :
      4 * h3DuhamelQuarterHistoryPowerCoefficient
            ν (2 * A) (2 * A) *
          s ^ ((1 : ℝ) / 4) +
        h3DuhamelQuarterSelectedRestartCoefficient ν A
        ≤
      h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t := by
    unfold h3DuhamelQuarterSelectedRestartLocalCoefficient
    exact
      add_le_add
        (mul_le_mul_of_nonneg_left hTimePow hHistoryCoeff)
        (le_refl _)

  have hPowNonneg :
      0 ≤ (h : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg h.property _

  calc
    ‖h3SpectralFinHeatLerayDuhamel ν s hν W W -
        h3SpectralFinHeatLerayDuhamel ν t hν W W‖
        =
      ‖h3SpectralFinHeatLerayDuhamel ν t hν W W -
        h3SpectralFinHeatLerayDuhamel ν s hν W W‖ := by
          exact norm_sub_rev _ _
    _ =
      ‖h3SpectralFinHeatLerayDuhamel ν (s + (h : ℝ)) hν W W -
        h3SpectralFinHeatLerayDuhamel ν s hν W W‖ := by
          rw [hst]
    _ ≤
      (4 * h3DuhamelQuarterHistoryPowerCoefficient
            ν (2 * A) (2 * A) *
          s ^ ((1 : ℝ) / 4) +
        h3DuhamelQuarterSelectedRestartCoefficient ν A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) :=
      hInc
    _ ≤
      h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t *
        (h : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hCoeff hPowNonneg
    _ =
      h3DuhamelQuarterSelectedRestartLocalCoefficient ν A t *
        (t - s) ^ ((1 : ℝ) / 4) := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
