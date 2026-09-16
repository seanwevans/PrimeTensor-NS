import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongTransportPointwiseBound

/-!
# Selected--old weak--strong transport vector bound

The preceding file gives, for each component `j`,

    |D_j ((D · ∇)S_j)|
      ≤ B |D_j| (|D_x| + |D_y| + |D_z|).

This file performs the finite-dimensional bookkeeping that turns those three
componentwise estimates into one quadratic pointwise energy density.

The only inequality needed is the three-dimensional `ℓ¹`--`ℓ²` comparison

    (|a| + |b| + |c|)^2
      ≤ 3 (a^2 + b^2 + c^2).

Consequently,

    Σ_j |D_j ((D · ∇)S_j)|
      ≤ 3 B (D_x^2 + D_y^2 + D_z^2).

Nothing is integrated yet.  The next step can therefore pass directly to the
physical `L²` pairing once the selected branch supplies a uniform pointwise
gradient coefficient `B`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongTransportVectorBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three-dimensional `ℓ¹² ≤ 3 ℓ²²`. -/
theorem abs_sum_three_sq_le_three_sum_sq
    (a b c : ℝ) :
    (abs a + (abs b + abs c)) ^ 2
      ≤
    3 * (a ^ 2 + (b ^ 2 + c ^ 2)) := by
  have hab :
      0 ≤ (abs a - abs b) ^ 2 :=
    sq_nonneg (abs a - abs b)

  have hac :
      0 ≤ (abs a - abs c) ^ 2 :=
    sq_nonneg (abs a - abs c)

  have hbc :
      0 ≤ (abs b - abs c) ^ 2 :=
    sq_nonneg (abs b - abs c)

  nlinarith [sq_abs a, sq_abs b, sq_abs c]

/-- Nonnegative scaling of the three-dimensional `ℓ¹² ≤ 3 ℓ²²` estimate. -/
theorem mul_abs_sum_three_sq_le_three_mul_sum_sq
    (a b c B : ℝ)
    (hB : 0 ≤ B) :
    B * (abs a + (abs b + abs c)) ^ 2
      ≤
    3 * B * (a ^ 2 + (b ^ 2 + c ^ 2)) := by
  have h :=
    mul_le_mul_of_nonneg_left
      (abs_sum_three_sq_le_three_sum_sq a b c)
      hB

  calc
    B * (abs a + (abs b + abs c)) ^ 2
        ≤
      B * (3 * (a ^ 2 + (b ^ 2 + c ^ 2))) := h
    _ =
      3 * B * (a ^ 2 + (b ^ 2 + c ^ 2)) := by
        ring

/-- Pointwise Euclidean square of the selected-minus-old velocity difference. -/
noncomputable def selectedOldVelocityDifferenceSquarePointwise
    (selected old :
      PrimeTensor.SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (t : ℝ)
    (x : Point3) : ℝ :=
  ((selected t x).component xAxis - (old t x).component xAxis) ^ 2
    +
  (
    ((selected t x).component yAxis - (old t x).component yAxis) ^ 2
      +
    ((selected t x).component zAxis - (old t x).component zAxis) ^ 2
  )

/-- Summing the three componentwise weak--strong density estimates yields a
single quadratic pointwise energy bound. -/
theorem sum_abs_selectedOldDifference_mul_selectedGradientInteraction_le
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
      ≤
    3 * B *
      selectedOldVelocityDifferenceSquarePointwise
        selected old t x := by
  have hx :=
    abs_selectedOldDifference_mul_selectedGradientInteraction_le
      selected old t x xAxis B hB
      (hGradient xAxis xAxis)
      (hGradient xAxis yAxis)
      (hGradient xAxis zAxis)

  have hy :=
    abs_selectedOldDifference_mul_selectedGradientInteraction_le
      selected old t x yAxis B hB
      (hGradient yAxis xAxis)
      (hGradient yAxis yAxis)
      (hGradient yAxis zAxis)

  have hz :=
    abs_selectedOldDifference_mul_selectedGradientInteraction_le
      selected old t x zAxis B hB
      (hGradient zAxis xAxis)
      (hGradient zAxis yAxis)
      (hGradient zAxis zAxis)

  have hSum :
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
        ≤
      B
          *
        abs ((selected t x).component xAxis - (old t x).component xAxis)
          *
        selectedOldVelocityDifferenceL1Pointwise
          selected old t x
        +
      (
        B
            *
          abs ((selected t x).component yAxis - (old t x).component yAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
          +
        B
            *
          abs ((selected t x).component zAxis - (old t x).component zAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
      ) := by
    exact
      add_le_add
        hx
        (add_le_add hy hz)

  calc
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
        ≤
      B
          *
        abs ((selected t x).component xAxis - (old t x).component xAxis)
          *
        selectedOldVelocityDifferenceL1Pointwise
          selected old t x
        +
      (
        B
            *
          abs ((selected t x).component yAxis - (old t x).component yAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
          +
        B
            *
          abs ((selected t x).component zAxis - (old t x).component zAxis)
            *
          selectedOldVelocityDifferenceL1Pointwise
            selected old t x
      ) := hSum
    _ =
      B *
        (selectedOldVelocityDifferenceL1Pointwise
          selected old t x) ^ 2 := by
      unfold selectedOldVelocityDifferenceL1Pointwise
      ring
    _ ≤
      3 * B *
        selectedOldVelocityDifferenceSquarePointwise
          selected old t x := by
      unfold
        selectedOldVelocityDifferenceL1Pointwise
        selectedOldVelocityDifferenceSquarePointwise

      exact
        mul_abs_sum_three_sq_le_three_mul_sum_sq
          ((selected t x).component xAxis - (old t x).component xAxis)
          ((selected t x).component yAxis - (old t x).component yAxis)
          ((selected t x).component zAxis - (old t x).component zAxis)
          B
          hB

end

end Euclidean
end Bridge
end PrimeTensor
