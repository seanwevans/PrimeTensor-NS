import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.Kernel
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Mild.Physical.Restart.Radius.Closure

/-!
# Selected-restart quarter increment for the positive-lag Duhamel kernel

The positive-lag kernel estimate from `Quarter.Duhamel.Kernel` is stated in
terms of the actual H³ norms of its two inputs.  Along the Banach-selected
canonical restart path both inputs are uniformly bounded by `2A`.

This file performs that specialization and records the form needed under the
history integral: for every `s < t`, the kernel with lag `t-s` changes under
an additional heat increment by at most the same scalar majorant with both
state norms replaced by `2A`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped NNReal

noncomputable section

/-- The positive-lag quarter-kernel bound remains valid after replacing both
input norms by a common selected-restart bound `2A`. -/
theorem norm_h3SpectralVelocityHeatApplyNN_heatLerayVelocityApply_sub_le_quarter_of_norm_le_twoA
    {ν A τ : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (hτ : 0 < τ)
    (h : NNReal)
    (U V : H3SpectralFinVectorState)
    (hU : ‖U‖ ≤ 2 * A)
    (hV : ‖V‖ ≤ 2 * A) :
    ‖h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V) -
        h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V‖
      ≤
    h3DuhamelQuarterHistoryKernelMajorant
      ν τ (h : ℝ) (2 * A) (2 * A) := by
  have hBase :=
    norm_h3SpectralVelocityHeatApplyNN_heatLerayVelocityApply_sub_le_quarter
      hν hτ h U V

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hUV :
      ‖U‖ * ‖V‖ ≤ (2 * A) * (2 * A) := by
    exact
      mul_le_mul hU hV (norm_nonneg _) h2A

  have hPrefactor :
      0 ≤
        288 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * (τ / 2)))⁻¹ := by
    positivity [h3SobolevDeweightingConstant_nonneg]

  have hInner :
      288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹ * ‖U‖ * ‖V‖
        ≤
      288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹ * (2 * A) * (2 * A) := by
    calc
      288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹ * ‖U‖ * ‖V‖
          =
        (288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹) * (‖U‖ * ‖V‖) := by
          ring
      _ ≤
        (288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹) * ((2 * A) * (2 * A)) := by
          exact mul_le_mul_of_nonneg_left hUV hPrefactor
      _ =
        288 * h3SobolevDeweightingConstant *
            (Real.sqrt (ν * (τ / 2)))⁻¹ * (2 * A) * (2 * A) := by
          ring

  have hQ :
      0 ≤ h3HeatQuarterIncrementCoefficient ν (τ / 2) (h : ℝ) :=
    h3HeatQuarterIncrementCoefficient_nonneg
      hν.le (by linarith : 0 ≤ τ / 2) h.property

  calc
    ‖h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V) -
        h3SpectralFinHeatLerayVelocityApply ν τ hν hτ U V‖
        ≤
      h3DuhamelQuarterHistoryKernelMajorant
        ν τ (h : ℝ) ‖U‖ ‖V‖ := hBase
    _ ≤
      h3DuhamelQuarterHistoryKernelMajorant
        ν τ (h : ℝ) (2 * A) (2 * A) := by
      unfold h3DuhamelQuarterHistoryKernelMajorant
      exact mul_le_mul_of_nonneg_left hInner hQ

/-- Selected-restart history form.  For every strict history time `s < t`,
the lag `t-s` is positive and the previous estimate applies to the selected
mild state at `s`. -/
theorem norm_h3SpectralVelocityHeatApplyNN_selectedRestart_heatLeray_history_sub_le_quarter
    {ν A s t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hst : s < t)
    (h : NNReal) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayVelocityApply
            ν (t - s) hν (sub_pos.mpr hst) (W s) (W s)) -
        h3SpectralFinHeatLerayVelocityApply
          ν (t - s) hν (sub_pos.mpr hst) (W s) (W s)‖
      ≤
    h3DuhamelQuarterHistoryKernelMajorant
      ν (t - s) (h : ℝ) (2 * A) (2 * A) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW : ‖W s‖ ≤ 2 * A := by
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  exact
    norm_h3SpectralVelocityHeatApplyNN_heatLerayVelocityApply_sub_le_quarter_of_norm_le_twoA
      hν hA.le (sub_pos.mpr hst) h (W s) (W s) hW hW

end

end Euclidean
end Bridge
end PrimeTensor
