import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Duhamel.Bound

/-!
# Fin-indexed pre-Leray velocity kernel

The antisymmetric vorticity flux is analytically useful, but it cannot be the
quadratic `duhamel x x` used by `H3HeatLerayEstimateData`, since

    x ⊗ x - x ⊗ x = 0.

The existing heat--Leray Picard layer is natively the velocity formulation.
Its quadratic tensor is therefore

    U ⊗ V,

followed by divergence, heat evolution, and finally the Leray projector.

This file closes the pre-Leray part.  The weighted H³ product costs
`16 C_deweight`; the three divergence directions cost `3`; hence

    ‖e^{νtΔ} div (U ⊗ V)‖
      ≤ 48 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖V‖.

Integrating the scalar singularity gives the pre-Leray time coefficient

    96 C_deweight (sqrt ν)⁻¹.

The next rung will insert the finite-dimensional Leray projection.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped ENNReal NNReal Interval

noncomputable section

/--
Heat evolution after Fourier divergence of the finite-index velocity tensor
product.
-/
noncomputable def h3SpectralFinVelocityHeatDivergenceApply
    (ν t : ℝ)
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState :=
  h3SpectralFinTensorHeatDivergenceApply
    ν t hν ht (h3SpectralFinOuterProduct U V)

/--
The complete one-time pre-Leray velocity nonlinear estimate.
-/
theorem norm_h3SpectralFinVelocityHeatDivergenceApply_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V‖
      ≤
    48 * h3SobolevDeweightingConstant *
      (Real.sqrt (ν * t))⁻¹ *
      ‖U‖ * ‖V‖ := by
  have hc :
      0 ≤ 3 * (Real.sqrt (ν * t))⁻¹ := by
    positivity

  calc
    ‖h3SpectralFinVelocityHeatDivergenceApply
        ν t hν ht U V‖
        ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        ‖h3SpectralFinOuterProduct U V‖ :=
      norm_h3SpectralFinTensorHeatDivergenceApply_le
        hν ht (h3SpectralFinOuterProduct U V)
    _ ≤
      3 * (Real.sqrt (ν * t))⁻¹ *
        (16 * h3SobolevDeweightingConstant * ‖U‖ * ‖V‖) :=
      mul_le_mul_of_nonneg_left
        (norm_h3SpectralFinOuterProduct_le U V)
        hc
    _ =
      48 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖V‖ := by
      ring

/--
Concrete square-root-time coefficient for the pre-Leray velocity Duhamel term.
-/
def h3VelocityDuhamelCoefficient
    (ν : ℝ) : ℝ :=
  96 * h3SobolevDeweightingConstant *
    (Real.sqrt ν)⁻¹

/-- The pre-Leray velocity Duhamel coefficient is nonnegative. -/
theorem h3VelocityDuhamelCoefficient_nonneg
    {ν : ℝ}
    (hν : 0 < ν) :
    0 ≤ h3VelocityDuhamelCoefficient ν := by
  unfold h3VelocityDuhamelCoefficient
  positivity [h3SobolevDeweightingConstant_nonneg]

/--
Scalar integration of the complete `48 C_deweight` velocity envelope.
-/
theorem h3_velocityKernelEnvelope_integral
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t,
        48 * h3SobolevDeweightingConstant *
          h3ViscousTimeSingularKernel ν t s)
      =
    h3VelocityDuhamelCoefficient ν *
      Real.sqrt t := by
  unfold h3ViscousTimeSingularKernel
  calc
    (∫ s in (0 : ℝ)..t,
        48 * h3SobolevDeweightingConstant *
          (Real.sqrt (ν * (t - s)))⁻¹)
        =
      (48 * h3SobolevDeweightingConstant) *
        (∫ s in (0 : ℝ)..t,
          (Real.sqrt (ν * (t - s)))⁻¹) := by
            rw [intervalIntegral.integral_const_mul]
    _ =
      (48 * h3SobolevDeweightingConstant) *
        (2 * (Real.sqrt ν)⁻¹ * Real.sqrt t) := by
          rw [h3_viscousTimeSingularKernel_integral hν ht]
    _ =
      h3VelocityDuhamelCoefficient ν *
        Real.sqrt t := by
          unfold h3VelocityDuhamelCoefficient
          ring

end

end Euclidean
end Bridge
end PrimeTensor
