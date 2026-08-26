import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Path.Space
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.L2.Bridge

/-!
# Concrete L² H³ jet state for the mild restart problem

The abstract mild path space now has a concrete spatial Banach state.

For a three-component velocity field in three spatial dimensions, the
componentwise derivative roster through order three contains

    3 + 3^2 + 3^3 + 3^4 = 120

scalar L² fields.  We package these as a finite product of Mathlib `Lp` spaces.
The finite product carries the sup norm and is complete automatically.

This is deliberately a *jet state*: an arbitrary element need not satisfy the
compatibility relations required to be the derivative jet of one underlying
velocity field.  A later bridge will map actual H³ velocity data into this
state and record those compatibility constraints separately.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable local instance point3MeasureSpaceH3MildState :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Finite semantic coordinate roster -/

/-- Zeroth-order slots: one velocity component. -/
abbrev H3JetIndex0 : Type := Fin 3

/-- First-order slots: component and one derivative direction. -/
abbrev H3JetIndex1 : Type := Fin 3 × Fin 3

/-- Second-order slots: component and two derivative directions. -/
abbrev H3JetIndex2 : Type := Fin 3 × Fin 3 × Fin 3

/-- Third-order slots: component and three derivative directions. -/
abbrev H3JetIndex3 : Type := Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- Disjoint union of all scalar derivative slots through order three. -/
abbrev H3JetIndex : Type :=
  Sum H3JetIndex0
    (Sum H3JetIndex1
      (Sum H3JetIndex2 H3JetIndex3))

/-- The H³ jet has exactly 120 scalar L² coordinates. -/
theorem h3JetIndex_card :
    Fintype.card H3JetIndex = 120 := by
  native_decide

/-- One real scalar `L²(Point3)` state. -/
abbrev H3ScalarL2 : Type :=
  MeasureTheory.Lp ℝ 2 (volume : Measure Point3)

/--
Concrete complete spatial state used by the mild Picard problem.

Mathlib equips this finite function space with the sup norm.
-/
abbrev H3L2JetState : Type :=
  H3JetIndex → H3ScalarL2

/-- The concrete normalized mild path space. -/
abbrev H3L2JetPath : Type :=
  H3Path H3L2JetState

/-- Heat--Leray data specialized all the way to the concrete L² jet path. -/
abbrev H3L2JetHeatLerayEstimateData : Type :=
  H3PathHeatLerayEstimateData H3L2JetState

/-! ## Banach-space facts -/

/-- The scalar `L²` coordinate space is complete. -/
theorem h3ScalarL2_complete :
    CompleteSpace H3ScalarL2 := by
  infer_instance

/-- The finite 120-coordinate jet state is complete. -/
theorem h3L2JetState_complete :
    CompleteSpace H3L2JetState := by
  infer_instance

/-- The concrete normalized H³-jet path space is complete. -/
theorem h3L2JetPath_complete :
    CompleteSpace H3L2JetPath := by
  infer_instance

/-- Every scalar L² coordinate is controlled by the finite-product sup norm. -/
theorem h3L2Jet_coordinate_norm_le
    (J : H3L2JetState)
    (a : H3JetIndex) :
    ‖J a‖ ≤ ‖J‖ := by
  exact
    (pi_norm_le_iff_of_nonneg (norm_nonneg J)).1
      le_rfl a

/-! ## Sum-of-squares energy on the finite jet -/

/-- Unnormalized finite sum of squared L² coordinate norms. -/
noncomputable def h3L2JetSquareEnergy
    (J : H3L2JetState) : ℝ :=
  ∑ a : H3JetIndex, ‖J a‖ ^ 2

/-- The finite jet energy is nonnegative. -/
theorem h3L2JetSquareEnergy_nonneg
    (J : H3L2JetState) :
    0 ≤ h3L2JetSquareEnergy J := by
  unfold h3L2JetSquareEnergy
  exact
    Finset.sum_nonneg
      (fun a _ => sq_nonneg ‖J a‖)

/-- Every individual squared coordinate is bounded by total jet energy. -/
theorem h3L2Jet_coordinate_sq_le_energy
    (J : H3L2JetState)
    (a : H3JetIndex) :
    ‖J a‖ ^ 2 ≤ h3L2JetSquareEnergy J := by
  unfold h3L2JetSquareEnergy
  apply
    Finset.single_le_sum
      (fun b _ => sq_nonneg ‖J b‖)
  simp

/--
The sum-of-squares jet energy is bounded by coordinate count times the squared
sup norm.  This is the finite-dimensional norm-equivalence direction needed by
the Picard radius bookkeeping.
-/
theorem h3L2JetSquareEnergy_le_card_mul_norm_sq
    (J : H3L2JetState) :
    h3L2JetSquareEnergy J
      ≤ (Fintype.card H3JetIndex : ℝ) * ‖J‖ ^ 2 := by
  unfold h3L2JetSquareEnergy
  calc
    (∑ a : H3JetIndex, ‖J a‖ ^ 2)
        ≤ ∑ _a : H3JetIndex, ‖J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro a ha
          have hcoord : ‖J a‖ ≤ ‖J‖ :=
            h3L2Jet_coordinate_norm_le J a
          have hleft : 0 ≤ ‖J a‖ := norm_nonneg _
          have hright : 0 ≤ ‖J‖ := norm_nonneg _
          nlinarith
    _ = (Fintype.card H3JetIndex : ℝ) * ‖J‖ ^ 2 := by
      simp

/-- Numerically, the preceding estimate has the fixed coefficient 120. -/
theorem h3L2JetSquareEnergy_le_120_mul_norm_sq
    (J : H3L2JetState) :
    h3L2JetSquareEnergy J ≤ 120 * ‖J‖ ^ 2 := by
  simpa [h3JetIndex_card] using
    h3L2JetSquareEnergy_le_card_mul_norm_sq J

/-- Pointwise coordinate control along a normalized concrete mild path. -/
theorem h3L2JetPath_coordinate_norm_le
    (u : H3L2JetPath)
    (s : H3UnitTime)
    (a : H3JetIndex) :
    ‖u s a‖ ≤ ‖u‖ := by
  calc
    ‖u s a‖ ≤ ‖u s‖ :=
      h3L2Jet_coordinate_norm_le (u s) a
    _ ≤ ‖u‖ :=
      h3Path_norm_apply_le_norm u s

end Euclidean
end Bridge
end PrimeTensor
