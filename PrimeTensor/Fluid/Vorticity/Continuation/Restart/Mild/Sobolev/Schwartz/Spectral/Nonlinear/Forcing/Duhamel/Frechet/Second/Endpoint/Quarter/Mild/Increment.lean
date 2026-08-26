import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.Orbit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Quarter-Hölder increment of the selected mild path

At positive base time `t`, the selected mild solution has the exact splitting

    W(t) = H_t U₀ + D_t(W,W).

The free heat increment is quarter-Hölder by `Quarter.Heat.State` (with its
coefficient factored through `Quarter.Heat.Orbit`), while the nonlinear
Duhamel increment is quarter-Hölder by `Quarter.Duhamel.Increment`.

Adding those two estimates closes a quarter-power modulus for the actual
selected mild path on every admissible positive substep of the canonical
restart interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

/-- Time-local coefficient for a positive-base quarter-Hölder increment of the
selected mild path. -/
noncomputable def h3MildQuarterSelectedRestartIncrementCoefficient
    (ν A t : ℝ) : ℝ :=
  h3HeatQuarterOrbitCoefficient ν t * A +
    4 * h3DuhamelQuarterHistoryPowerCoefficient
        ν (2 * A) (2 * A) *
      t ^ ((1 : ℝ) / 4) +
    h3DuhamelQuarterSelectedRestartCoefficient ν A

/-- The selected mild path is quarter-Hölder across every positive-base
substep which remains inside the canonical restart interval. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_add_time_sub_le_quarter
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (h : NNReal)
    (hh : 0 < h)
    (hthR : t + (h : ℝ) ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖W (t + (h : ℝ)) - W t‖
      ≤
    h3MildQuarterSelectedRestartIncrementCoefficient ν A t *
      (h : ℝ) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D₀ : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W

  let D₁ : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel ν (t + (h : ℝ)) hν W W

  have ht0 : 0 ≤ t := ht.le
  have hhReal : 0 < (h : ℝ) := by
    exact_mod_cast hh
  have hh0 : 0 ≤ (h : ℝ) := hhReal.le
  have hth0 : 0 ≤ t + (h : ℝ) := add_nonneg ht0 hh0
  have htR : t ≤ h3FinHeatLerayRestartRadius ν A := by
    exact le_trans (le_add_of_nonneg_right hh0) hthR
  have hhR : (h : ℝ) ≤ h3FinHeatLerayRestartRadius ν A := by
    linarith

  let qt : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨t, ht0, htR⟩
  let qth : Set.Icc (0 : ℝ) (h3FinHeatLerayRestartRadius ν A) :=
    ⟨t + (h : ℝ), hth0, hthR⟩

  let tNN : NNReal := NNReal.mk t ht0

  have htNN : (tNN : ℝ) = t := by
    rfl

  have hthNN :
      NNReal.mk (t + (h : ℝ)) hth0 = tNN + h := by
    apply Subtype.ext
    change t + (h : ℝ) = (tNN : ℝ) + (h : ℝ)
    exact (congrArg (fun x : ℝ => x + (h : ℝ)) htNN).symm

  have hMildT0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      qt
  have hqtNN :
      h3PhysicalTimePointNN qt = tNN := by
    rfl
  rw [hqtNN] at hMildT0
  have hMildT :
      h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ + D₀ = W t := by
    simpa only [W, D₀, qt,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildT0

  have hMildTH0 :=
    h3SpectralFinHeatLerayPhysicalMildSolution_satisfies_mild_at
      hν
      (h3FinHeatLerayRestartRadius_pos ν hA).le
      U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_smallness ν hA.le)
      qth
  have hqthNN :
      h3PhysicalTimePointNN qth =
        NNReal.mk (t + (h : ℝ)) hth0 := by
    rfl
  rw [hqthNN, hthNN] at hMildTH0
  have hMildTH :
      h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ + D₁
        = W (t + (h : ℝ)) := by
    simpa only [W, D₁, qth,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension,
      h3SpectralFinHeatLerayPhysicalMildSolution_apply] using hMildTH0

  have hHeatCoeff :
      0 ≤ h3HeatQuarterIncrementCoefficient ν t (h : ℝ) := by
    exact
      h3HeatQuarterIncrementCoefficient_nonneg
        hν.le ht0 h.property

  have hHeat :
      ‖h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖
        ≤
      (h3HeatQuarterOrbitCoefficient ν t * A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
    calc
      ‖h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖
          ≤
        h3HeatQuarterIncrementCoefficient ν t (h : ℝ) * ‖U₀‖ := by
          simpa only [tNN, NNReal.coe_mk] using
            (norm_h3SpectralVelocityHeatApplyNN_add_sub_le_quarter
              hν tNN h ht U₀)
      _ ≤
        h3HeatQuarterIncrementCoefficient ν t (h : ℝ) * A := by
          exact mul_le_mul_of_nonneg_left hU₀ hHeatCoeff
      _ =
        (h3HeatQuarterOrbitCoefficient ν t * A) *
          (h : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [h3HeatQuarterIncrementCoefficient_eq_orbit_mul_rpow
            (ν := ν) (a := t) (h := (h : ℝ)) hν.le h.property]
          ring

  have hDuhamel :
      ‖D₁ - D₀‖
        ≤
      (4 * h3DuhamelQuarterHistoryPowerCoefficient
            ν (2 * A) (2 * A) *
          t ^ ((1 : ℝ) / 4) +
        h3DuhamelQuarterSelectedRestartCoefficient ν A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
    dsimp only [D₁, D₀, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_add_time_sub_le_quarter
        hν U₀ hA hU₀ ht h hh hhR

  change
    ‖W (t + (h : ℝ)) - W t‖
      ≤
    h3MildQuarterSelectedRestartIncrementCoefficient ν A t *
      (h : ℝ) ^ ((1 : ℝ) / 4)

  rw [← hMildTH, ← hMildT]

  have hDecomp :
      (h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ + D₁) -
          (h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀ + D₀)
        =
      (h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀) +
        (D₁ - D₀) := by
    abel
  rw [hDecomp]

  calc
    ‖(h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀) +
        (D₁ - D₀)‖
        ≤
      ‖h3SpectralVelocityHeatApplyNN ν hν.le (tNN + h) U₀ -
          h3SpectralVelocityHeatApplyNN ν hν.le tNN U₀‖ +
        ‖D₁ - D₀‖ :=
      norm_add_le _ _
    _ ≤
      (h3HeatQuarterOrbitCoefficient ν t * A) *
          (h : ℝ) ^ ((1 : ℝ) / 4) +
        (4 * h3DuhamelQuarterHistoryPowerCoefficient
              ν (2 * A) (2 * A) *
            t ^ ((1 : ℝ) / 4) +
          h3DuhamelQuarterSelectedRestartCoefficient ν A) *
          (h : ℝ) ^ ((1 : ℝ) / 4) :=
      add_le_add hHeat hDuhamel
    _ =
      h3MildQuarterSelectedRestartIncrementCoefficient ν A t *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
      unfold h3MildQuarterSelectedRestartIncrementCoefficient
      ring

end

end Euclidean
end Bridge
end PrimeTensor
