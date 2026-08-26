import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Continuity
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Spatial continuity of the Fin-indexed H³ heat--Leray kernel

The previous continuity checkpoint fixes the spatial inputs and varies the
positive heat lag.  For the retarded path kernel we also need continuity in
the two H³ velocity inputs.

At fixed positive lag the genuine heat--Leray kernel is additive in each input,
by `FinHeatLerayBilinear`, and satisfies

    ‖K_t(U,V)‖
      ≤ 288 C_deweight (sqrt (ν t))⁻¹ ‖U‖ ‖V‖.

Thus, after fixing one input, the other slot is a bounded additive homomorphism.
Mathlib's `AddMonoidHomClass.continuous_of_bound` converts exactly that bound
into continuity.  No scalar-linearity theorem is needed.

This gives the spatial half of the joint retarded-kernel continuity argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ## Additive-hom packaging -/

/-- The heat--Leray kernel as an additive hom in its first velocity input. -/
noncomputable def h3SpectralFinHeatLerayLeftAddHom
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (V : H3SpectralFinVectorState) :
    H3SpectralFinVectorState →+
      H3SpectralFinVectorState where
  toFun := fun U =>
    h3SpectralFinHeatLerayVelocityApply
      ν t hν ht U V
  map_zero' := by
    have h :=
      h3SpectralFinHeatLerayVelocityApply_sub_left
        hν ht
        (0 : H3SpectralFinVectorState)
        (0 : H3SpectralFinVectorState)
        V
    simpa using h
  map_add' := by
    intro U W
    exact
      h3SpectralFinHeatLerayVelocityApply_add_left
        hν ht U W V

/-- The heat--Leray kernel as an additive hom in its second velocity input. -/
noncomputable def h3SpectralFinHeatLerayRightAddHom
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralFinVectorState) :
    H3SpectralFinVectorState →+
      H3SpectralFinVectorState where
  toFun := fun V =>
    h3SpectralFinHeatLerayVelocityApply
      ν t hν ht U V
  map_zero' := by
    have h :=
      h3SpectralFinHeatLerayVelocityApply_sub_right
        hν ht
        U
        (0 : H3SpectralFinVectorState)
        (0 : H3SpectralFinVectorState)
    simpa using h
  map_add' := by
    intro V W
    exact
      h3SpectralFinHeatLerayVelocityApply_add_right
        hν ht U V W

/-! ## Boundedness in one slot -/

/-- Fixed-second-input operator bound. -/
theorem norm_h3SpectralFinHeatLerayLeftAddHom_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (V U : H3SpectralFinVectorState) :
    ‖h3SpectralFinHeatLerayLeftAddHom
        hν ht V U‖
      ≤
    (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖V‖) *
      ‖U‖ := by
  have h :=
    norm_h3SpectralFinHeatLerayVelocityApply_le
      hν ht U V
  calc
    ‖h3SpectralFinHeatLerayLeftAddHom
        hν ht V U‖
        =
      ‖h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V‖ := by
          rfl
    _ ≤
      288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖V‖ :=
      h
    _ =
      (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖V‖) *
        ‖U‖ := by
          ring

/-- Fixed-first-input operator bound. -/
theorem norm_h3SpectralFinHeatLerayRightAddHom_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U V : H3SpectralFinVectorState) :
    ‖h3SpectralFinHeatLerayRightAddHom
        hν ht U V‖
      ≤
    (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖U‖) *
      ‖V‖ := by
  have h :=
    norm_h3SpectralFinHeatLerayVelocityApply_le
      hν ht U V
  calc
    ‖h3SpectralFinHeatLerayRightAddHom
        hν ht U V‖
        =
      ‖h3SpectralFinHeatLerayVelocityApply
        ν t hν ht U V‖ := by
          rfl
    _ ≤
      288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ *
        ‖U‖ * ‖V‖ :=
      h
    _ =
      (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖U‖) *
        ‖V‖ := by
          ring

/-! ## Separate spatial continuity -/

/-- At fixed positive lag and fixed second input, the kernel is continuous in the first input. -/
theorem continuous_h3SpectralFinHeatLerayVelocityApply_left
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (V : H3SpectralFinVectorState) :
    Continuous
      (fun U : H3SpectralFinVectorState =>
        h3SpectralFinHeatLerayVelocityApply
          ν t hν ht U V) := by
  exact
    AddMonoidHomClass.continuous_of_bound
      (h3SpectralFinHeatLerayLeftAddHom hν ht V)
      (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖V‖)
      (norm_h3SpectralFinHeatLerayLeftAddHom_le
        hν ht V)

/-- At fixed positive lag and fixed first input, the kernel is continuous in the second input. -/
theorem continuous_h3SpectralFinHeatLerayVelocityApply_right
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (U : H3SpectralFinVectorState) :
    Continuous
      (fun V : H3SpectralFinVectorState =>
        h3SpectralFinHeatLerayVelocityApply
          ν t hν ht U V) := by
  exact
    AddMonoidHomClass.continuous_of_bound
      (h3SpectralFinHeatLerayRightAddHom hν ht U)
      (288 * h3SobolevDeweightingConstant *
        (Real.sqrt (ν * t))⁻¹ * ‖U‖)
      (norm_h3SpectralFinHeatLerayRightAddHom_le
        hν ht U)

end

end Euclidean
end Bridge
end PrimeTensor
