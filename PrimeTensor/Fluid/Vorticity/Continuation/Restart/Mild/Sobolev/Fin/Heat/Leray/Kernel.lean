import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Leray.Multiplier

/-!
# Fin-indexed H³ heat--Leray velocity kernel

The previous two checkpoints provide:

* the pre-Leray velocity estimate

      ‖e^{νtΔ} div (U ⊗ V)‖
        ≤ 48 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖V‖,

* the finite-product Leray multiplier estimate

      ‖P G‖ ≤ 6 ‖G‖.

Composing them gives the actual instantaneous heat--Leray bilinear kernel

      P e^{νtΔ} div (U ⊗ V)

with the concrete bound

      ≤ 288 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖V‖.

Integrating the scalar reciprocal-square-root envelope gives the time
coefficient

      576 C_deweight (sqrt ν)⁻¹.

This is the constant that will feed the concrete `H3HeatLerayEstimateData`
instance once the retarded-time path integral and the bilinear subtraction
identity are packaged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Interval

noncomputable section

/--
The genuine finite-indexed heat--Leray velocity kernel.
-/
noncomputable def h3SpectralFinHeatLerayVelocityApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinLerayApply
    (h3SpectralFinVelocityHeatDivergenceApply
      ν t hν ht U V)

/--
Concrete instantaneous H³ heat--Leray bilinear estimate.
-/
theorem norm_h3SpectralFinHeatLerayVelocityApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V‖
      ≤
    288 * h3SobolevDeweightingConstant *
      (Real.sqrt (ν * t))⁻¹ *
      ‖U‖ * ‖V‖ := by
  have hPre :
      ‖h3SpectralFinVelocityHeatDivergenceApply
          ν t hν ht U V‖
        ≤
      48 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖V‖ :=
    norm_h3SpectralFinVelocityHeatDivergenceApply_le
      hν ht U V

  calc
    ‖h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V‖
        ≤
      6 *
        ‖h3SpectralFinVelocityHeatDivergenceApply
          ν t hν ht U V‖ := by
            unfold h3SpectralFinHeatLerayVelocityApply
            exact
              norm_h3SpectralFinLerayApply_le
                (h3SpectralFinVelocityHeatDivergenceApply
                  ν t hν ht U V)
    _ ≤
      6 *
        (48 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * t))⁻¹ *
          ‖U‖ * ‖V‖) :=
      mul_le_mul_of_nonneg_left
        hPre
        (by norm_num)
    _ =
      288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖V‖ := by
          ring

/--
Concrete square-root-time coefficient for the heat--Leray velocity Duhamel
term.
-/
def h3HeatLerayDuhamelCoefficient
    (ν : ℝ) : ℝ :=
  576 * h3SobolevDeweightingConstant *
    (Real.sqrt ν)⁻¹

/-- The heat--Leray Duhamel coefficient is nonnegative. -/
theorem h3HeatLerayDuhamelCoefficient_nonneg
    {ν : ℝ}
    (hν : 0 < ν) :
    0 ≤ h3HeatLerayDuhamelCoefficient ν := by
  unfold h3HeatLerayDuhamelCoefficient
  positivity [h3SobolevDeweightingConstant_nonneg]

/--
Scalar integration of the full `288 C_deweight` heat--Leray envelope.
-/
theorem h3_heatLerayKernelEnvelope_integral
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        288 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s)
      =
    h3HeatLerayDuhamelCoefficient ν *
      Real.sqrt t := by
  unfold h3ViscousTimeSingularKernel
  calc
    (∫ s in (0 : ℝ)..t,
        288 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * (t - s)))⁻¹)
        =
      (288 * h3SobolevDeweightingConstant) *
        (∫ s in (0 : ℝ)..t,
          (Real.sqrt (ν * (t - s)))⁻¹) := by
            rw [intervalIntegral.integral_const_mul]
    _ =
      (288 * h3SobolevDeweightingConstant) *
        (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
          rw [h3_viscousTimeSingularKernel_integral hν ht]
    _ =
      h3HeatLerayDuhamelCoefficient ν *
        Real.sqrt t := by
          unfold h3HeatLerayDuhamelCoefficient
          ring

end

end Euclidean
end Bridge
end PrimeTensor
