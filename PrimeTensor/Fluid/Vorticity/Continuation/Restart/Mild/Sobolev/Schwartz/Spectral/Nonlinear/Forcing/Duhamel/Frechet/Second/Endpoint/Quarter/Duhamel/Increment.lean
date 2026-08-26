import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Holder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Physical.Cocycle

/-!
# Quarter-Hölder increment of the selected-path Duhamel term

The full Duhamel increment from `t` to `t+h` has two pieces.  The physical
Duhamel cocycle gives

    D_{t+h}(W,W) - D_t(W,W)
      = (H_h D_t(W,W) - D_t(W,W)) + R(t,h).

The first term is the old-history heat increment closed in
`Quarter.Duhamel.History.Bound`; the second is the canonical restart remainder
closed in `Quarter.Duhamel.Holder`.  Combining those estimates yields one
quarter-power modulus for the actual Duhamel path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- The selected-path Duhamel term is quarter-Hölder across a positive base
time, with the old-history and fresh-remainder coefficients kept explicit. -/
theorem norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_add_time_sub_le_quarter
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (h : NNReal)
    (hh : 0 < h)
    (hhR : (h : ℝ) ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralFinHeatLerayDuhamel
          ν (t + (h : ℝ)) hν W W -
        h3SpectralFinHeatLerayDuhamel ν t hν W W‖
      ≤
    (4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
        t ^ ((1 : ℝ) / 4) +
      h3DuhamelQuarterSelectedRestartCoefficient ν A) *
      (h : ℝ) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W

  let R : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν t hν W W h

  have hhReal : 0 < (h : ℝ) := by
    exact_mod_cast hh

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hWbound : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hhNN :
      NNReal.mk (h : ℝ) hhReal.le = h := by
    apply Subtype.ext
    simp

  have hCocycle :
      h3SpectralFinHeatLerayDuhamel
          ν (t + (h : ℝ)) hν W W
        =
      h3SpectralVelocityHeatApplyNN ν hν.le h D + R := by
    have hC :=
      h3SpectralFinHeatLerayDuhamel_shifted_add_time_of_continuous
        (a := (0 : ℝ))
        (b := t)
        (c := (h : ℝ))
        (MU := 2 * A)
        (MV := 2 * A)
        hν ht hhReal h2A h2A
        W W hWcont hWcont hWbound hWbound
    rw [hhNN] at hC
    simpa only [add_zero, D, R,
      h3SpectralFinHeatLerayDuhamelRestartRemainder] using hC

  have hHistory :
      ‖h3SpectralVelocityHeatApplyNN ν hν.le h D - D‖
        ≤
      4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) *
        t ^ ((1 : ℝ) / 4) := by
    dsimp only [D, W]
    exact
      norm_h3DuhamelQuarterSelectedHistory_heatDuhamelDifference_le
        hν U₀ hA hU₀ ht.le h

  have hRemainder :
      ‖R‖ ≤
        h3DuhamelQuarterSelectedRestartCoefficient ν A *
          (h : ℝ) ^ ((1 : ℝ) / 4) := by
    dsimp only [R, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le_quarter_of_le_restartRadius
        hν U₀ hA hU₀ h hhR

  change
    ‖h3SpectralFinHeatLerayDuhamel
          ν (t + (h : ℝ)) hν W W - D‖
      ≤
    (4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
        t ^ ((1 : ℝ) / 4) +
      h3DuhamelQuarterSelectedRestartCoefficient ν A) *
      (h : ℝ) ^ ((1 : ℝ) / 4)

  rw [hCocycle]
  have hDecomp :
      h3SpectralVelocityHeatApplyNN ν hν.le h D + R - D
        =
      (h3SpectralVelocityHeatApplyNN ν hν.le h D - D) + R := by
    abel
  rw [hDecomp]

  calc
    ‖(h3SpectralVelocityHeatApplyNN ν hν.le h D - D) + R‖
        ≤
      ‖h3SpectralVelocityHeatApplyNN ν hν.le h D - D‖ + ‖R‖ :=
        norm_add_le _ _
    _ ≤
      4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) *
        t ^ ((1 : ℝ) / 4) +
      h3DuhamelQuarterSelectedRestartCoefficient ν A *
        (h : ℝ) ^ ((1 : ℝ) / 4) :=
      add_le_add hHistory hRemainder
    _ =
      (4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
        t ^ ((1 : ℝ) / 4) +
      h3DuhamelQuarterSelectedRestartCoefficient ν A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
