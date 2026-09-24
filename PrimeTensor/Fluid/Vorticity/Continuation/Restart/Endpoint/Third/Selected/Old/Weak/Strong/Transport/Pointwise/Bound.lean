import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Transport.Cancellation

/-!
# Selected--old weak--strong transport pointwise bound

After the old-velocity pure-transport term cancels, the surviving convection
piece is

    ((S - O) · ∇)S.

This file isolates the elementary pointwise estimate needed for the eventual
relative-energy bound.

If every coordinate derivative of the selected component `S_j` is bounded in
absolute value by `B`, then

    |((S-O) · ∇)S_j|
      ≤ B (|D_x| + |D_y| + |D_z|),

where `D = S - O`.  Multiplying by `|D_j|` gives the corresponding
relative-energy density estimate.

Nothing is integrated here.  In particular this increment does not yet choose
the concrete selected restart branch, prove a uniform gradient bound, or pass
from coordinatewise densities to the physical vector `L²` norm.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportPointwiseBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Elementary three-term dot-product estimate with one common coefficient
bound. -/
theorem abs_threeTermDot_le_commonBound
    (a b c gx gy gz B : ℝ)
    (hB : 0 ≤ B)
    (hgx : abs gx ≤ B)
    (hgy : abs gy ≤ B)
    (hgz : abs gz ≤ B) :
    abs (a * gx + (b * gy + c * gz))
      ≤
    B * (abs a + (abs b + abs c)) := by
  have hax :
      abs a * abs gx ≤ abs a * B :=
    mul_le_mul_of_nonneg_left
      hgx
      (abs_nonneg a)

  have hby :
      abs b * abs gy ≤ abs b * B :=
    mul_le_mul_of_nonneg_left
      hgy
      (abs_nonneg b)

  have hcz :
      abs c * abs gz ≤ abs c * B :=
    mul_le_mul_of_nonneg_left
      hgz
      (abs_nonneg c)

  calc
    abs (a * gx + (b * gy + c * gz))
        ≤
      abs (a * gx) + abs (b * gy + c * gz) := by
        exact abs_add_le _ _
    _ ≤
      abs (a * gx) + (abs (b * gy) + abs (c * gz)) := by
        exact
          add_le_add
            le_rfl
            (abs_add_le (b * gy) (c * gz))
    _ =
      abs a * abs gx + (abs b * abs gy + abs c * abs gz) := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤
      abs a * B + (abs b * B + abs c * B) := by
        exact
          add_le_add
            hax
            (add_le_add hby hcz)
    _ =
      B * (abs a + (abs b + abs c)) := by
        ring

/-- Pointwise `ℓ¹` size of the selected-minus-old velocity difference. -/
noncomputable def selectedOldVelocityDifferenceL1Pointwise
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3) : ℝ :=
  abs ((selected t x).component xAxis - (old t x).component xAxis)
    +
  (
    abs ((selected t x).component yAxis - (old t x).component yAxis)
      +
    abs ((selected t x).component zAxis - (old t x).component zAxis)
  )

/-- A uniform coordinate-gradient bound on the selected `j` component controls
the surviving weak--strong convection interaction pointwise. -/
theorem abs_realAdvectionSelectedGradientDifferenceComponent_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hx :
      abs
        (spatial3.d
          xAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B)
    (hy :
      abs
        (spatial3.d
          yAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B)
    (hz :
      abs
        (spatial3.d
          zAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B) :
    abs
        (realAdvectionSelectedGradientDifferenceComponent
          selected old t x j)
      ≤
    B *
      selectedOldVelocityDifferenceL1Pointwise
        selected old t x := by
  unfold
    realAdvectionSelectedGradientDifferenceComponent
    selectedOldVelocityDifferenceL1Pointwise

  exact
    abs_threeTermDot_le_commonBound
      ((selected t x).component xAxis - (old t x).component xAxis)
      ((selected t x).component yAxis - (old t x).component yAxis)
      ((selected t x).component zAxis - (old t x).component zAxis)
      (spatial3.d
        xAxis
        (fun y => (selected t y).component j)
        x)
      (spatial3.d
        yAxis
        (fun y => (selected t y).component j)
        x)
      (spatial3.d
        zAxis
        (fun y => (selected t y).component j)
        x)
      B
      hB hx hy hz

/-- Pointwise relative-energy density estimate for one component. -/
theorem abs_selectedOldDifference_mul_selectedGradientInteraction_le
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three)
    (B : ℝ)
    (hB : 0 ≤ B)
    (hx :
      abs
        (spatial3.d
          xAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B)
    (hy :
      abs
        (spatial3.d
          yAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B)
    (hz :
      abs
        (spatial3.d
          zAxis
          (fun y => (selected t y).component j)
          x)
        ≤ B) :
    abs
        (
          ((selected t x).component j - (old t x).component j)
            *
          realAdvectionSelectedGradientDifferenceComponent
            selected old t x j
        )
      ≤
    B
      *
    abs ((selected t x).component j - (old t x).component j)
      *
    selectedOldVelocityDifferenceL1Pointwise
      selected old t x := by
  rw [abs_mul]

  have hInteraction :=
    abs_realAdvectionSelectedGradientDifferenceComponent_le
      selected old t x j B hB hx hy hz

  calc
    abs ((selected t x).component j - (old t x).component j)
      *
    abs
      (realAdvectionSelectedGradientDifferenceComponent
        selected old t x j)
        ≤
    abs ((selected t x).component j - (old t x).component j)
      *
    (
      B *
      selectedOldVelocityDifferenceL1Pointwise
        selected old t x
    ) := by
      exact
        mul_le_mul_of_nonneg_left
          hInteraction
          (abs_nonneg _)
    _ =
      B
        *
      abs ((selected t x).component j - (old t x).component j)
        *
      selectedOldVelocityDifferenceL1Pointwise
        selected old t x := by
      ring

end

end Euclidean
end Bridge
end PrimeTensor
