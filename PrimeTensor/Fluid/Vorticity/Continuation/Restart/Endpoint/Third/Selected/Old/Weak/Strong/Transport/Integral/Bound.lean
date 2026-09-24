import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Transport.Vector.Bound

/-!
# Selected--old weak--strong transport integral bound

The preceding module proves the pointwise vector estimate

    Σ_j |D_j ((D · ∇)S_j)|
      ≤ 3 B |D|².

This file performs only the whole-space integration step.  It deliberately
keeps the square-density integral explicit:

    ∫ Σ_j |D_j ((D · ∇)S_j)|
      ≤ 3 B ∫ |D|².

The remaining quotient-level task is therefore isolated cleanly: identify the
right-hand square-density integral with the squared norm of the concrete
three-component physical `L²` Hilbert difference.

No new Navier--Stokes estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportIntegralBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongTransportIntegralBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (axisFintypeH3SelectedOldWeakStrongTransportIntegralBound Depth.three)
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Absolute value of the three component weak--strong interaction densities,
summed pointwise. -/
noncomputable def selectedOldWeakStrongAbsInteractionDensity
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3) : ℝ :=
  abs
      (
        ((selected t x).component xAxis - (old t x).component xAxis)
          *
        realAdvectionSelectedGradientDifferenceComponent
          selected old t x xAxis
      )
    +
  (
    abs
        (
          ((selected t x).component yAxis - (old t x).component yAxis)
            *
          realAdvectionSelectedGradientDifferenceComponent
            selected old t x yAxis
        )
      +
    abs
        (
          ((selected t x).component zAxis - (old t x).component zAxis)
            *
          realAdvectionSelectedGradientDifferenceComponent
            selected old t x zAxis
        )
  )

/-- Repackage the preceding pointwise vector estimate under one density name. -/
theorem selectedOldWeakStrongAbsInteractionDensity_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀
        j i : PrimeTensor.Axis Depth.three,
        abs
          (spatial3.d
            i
            (fun y => (selected t y).component j)
            x)
          ≤ B) :
    selectedOldWeakStrongAbsInteractionDensity
        selected old t x
      ≤
    3 * B *
      selectedOldVelocityDifferenceSquarePointwise
        selected old t x := by
  unfold selectedOldWeakStrongAbsInteractionDensity

  exact
    sum_abs_selectedOldDifference_mul_selectedGradientInteraction_le
      selected old t x B hB hGradient

/-- Whole-space integral form of the weak--strong pointwise estimate. -/
theorem integral_selectedOldWeakStrongAbsInteractionDensity_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hGradient :
      ∀
        (x : Point3)
        (j i : PrimeTensor.Axis Depth.three),
        abs
          (spatial3.d
            i
            (fun y => (selected t y).component j)
            x)
          ≤ B)
    (hInteraction :
      MeasureTheory.Integrable
        (selectedOldWeakStrongAbsInteractionDensity
          selected old t))
    (hSquare :
      MeasureTheory.Integrable
        (selectedOldVelocityDifferenceSquarePointwise
          selected old t)) :
    (∫ x : Point3,
      selectedOldWeakStrongAbsInteractionDensity
        selected old t x)
      ≤
    3 * B *
      (∫ x : Point3,
        selectedOldVelocityDifferenceSquarePointwise
          selected old t x) := by
  let majorant : Point3 → ℝ :=
    fun x =>
      3 * B *
        selectedOldVelocityDifferenceSquarePointwise
          selected old t x

  have hMajorant :
      MeasureTheory.Integrable majorant := by
    unfold majorant
    exact
      hSquare.const_mul (3 * B)

  have hPointwise :
      ∀ x : Point3,
        selectedOldWeakStrongAbsInteractionDensity
            selected old t x
          ≤
        majorant x := by
    intro x
    unfold majorant

    exact
      selectedOldWeakStrongAbsInteractionDensity_le
        selected old t x B hB
        (hGradient x)

  have hIntegralMono :
      (∫ x : Point3,
        selectedOldWeakStrongAbsInteractionDensity
          selected old t x)
        ≤
      ∫ x : Point3,
        majorant x := by
    exact
      MeasureTheory.integral_mono
        hInteraction
        hMajorant
        hPointwise

  calc
    (∫ x : Point3,
      selectedOldWeakStrongAbsInteractionDensity
        selected old t x)
        ≤
      ∫ x : Point3,
        majorant x := hIntegralMono
    _ =
      ∫ x : Point3,
        (3 * B) *
          selectedOldVelocityDifferenceSquarePointwise
            selected old t x := by
      rfl
    _ =
      3 * B *
        (∫ x : Point3,
          selectedOldVelocityDifferenceSquarePointwise
            selected old t x) := by
      rw [MeasureTheory.integral_const_mul]

end

end Euclidean
end Bridge
end PrimeTensor
