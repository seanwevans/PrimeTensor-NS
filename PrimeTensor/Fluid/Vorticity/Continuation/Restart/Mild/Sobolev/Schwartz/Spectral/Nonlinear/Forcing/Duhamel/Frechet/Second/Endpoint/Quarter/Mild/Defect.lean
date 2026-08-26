import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Holder
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Evolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Quarter-power defect of the selected mild restart from its heat orbit

The canonical restart equation writes the selected mild path as

    W(a + T) = H_T (W a) + R(a,T).

The preceding quarter-Hölder Duhamel layer bounds the canonical nonlinear
remainder by a fixed multiple of `T^(1/4)` on the canonical restart interval.
Consequently the selected mild step differs from the pure heat orbit launched
at its restart state by the same quarter-power modulus.

This isolates the nonlinear defect before the later endpoint path bookkeeping.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- On every admissible substep of the canonical selected restart interval,
the nonlinear defect from the heat orbit is quarter-Hölder in the elapsed
restart duration. -/
theorem norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_sub_heatRestart_le_quarter
    {ν A a : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (T : NNReal)
    (ha : 0 ≤ a)
    (hT : 0 < T)
    (haT : a + (T : ℝ) ≤ h3FinHeatLerayRestartRadius ν A) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖W (a + (T : ℝ)) -
        h3SpectralVelocityHeatApplyNN ν hν.le T (W a)‖
      ≤
    h3DuhamelQuarterSelectedRestartCoefficient ν A *
      (T : ℝ) ^ ((1 : ℝ) / 4) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let R : H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelRestartRemainder
      ν a hν W W T

  have hStep :
      h3SpectralVelocityHeatApplyNN ν hν.le T (W a) + R
        = W (a + (T : ℝ)) := by
    dsimp only [W, R,
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension]
    exact
      h3SpectralFinHeatLerayMildSolutionPhysicalExtension_restart_eq_restartRemainder
        (τ := h3FinHeatLerayRestartRadius ν A)
        (A := A)
        (a := a)
        hν
        (h3FinHeatLerayRestartRadius_pos ν hA).le
        U₀ hA hU₀
        (h3FinHeatLerayRestartRadius_smallness ν hA.le)
        T ha hT haT

  have hTR :
      (T : ℝ) ≤ h3FinHeatLerayRestartRadius ν A := by
    linarith

  have hR :
      ‖R‖ ≤
        h3DuhamelQuarterSelectedRestartCoefficient ν A *
          (T : ℝ) ^ ((1 : ℝ) / 4) := by
    dsimp only [R, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamelRestartRemainder_selectedRestart_le_quarter_of_le_restartRadius
        hν U₀ hA hU₀ T hTR

  change
    ‖W (a + (T : ℝ)) -
        h3SpectralVelocityHeatApplyNN ν hν.le T (W a)‖ ≤
      h3DuhamelQuarterSelectedRestartCoefficient ν A *
        (T : ℝ) ^ ((1 : ℝ) / 4)
  rw [← hStep]
  simpa only [add_sub_cancel_left] using hR

end

end Euclidean
end Bridge
end PrimeTensor
