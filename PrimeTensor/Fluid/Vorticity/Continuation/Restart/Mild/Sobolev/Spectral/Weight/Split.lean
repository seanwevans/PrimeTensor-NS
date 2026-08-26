import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.L1

/-!
# Splitting the exact H³ spectral weight across convolution frequencies

For the Fourier-side product estimate we need to move the exact H³ weight

    W₃(ξ)² = 1 + q(ξ) + q(ξ)² + q(ξ)³,
    q(ξ) = (2π)² ‖ξ‖²

onto either factor of a convolution.

The key estimate proved here is the coarse but explicit bound

    W₃(ξ) ≤ 8 * (W₃(η) + W₃(ξ - η)).

The constant is intentionally not optimized.  It is chosen so the proof uses
only the norm triangle inequality and elementary polynomial inequalities.

This is the weight-algebra input for the subsequent `L¹ * L² → L²`
convolution estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

/-! ## Elementary polynomial inequalities -/

/-- The square of a sum is bounded by twice the sum of squares. -/
theorem sq_add_le_two_mul_sum_sq
    (a b : ℝ) :
    (a + b) ^ 2
      ≤
    2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/--
For nonnegative reals, the cube of a sum is bounded by four times the sum
of cubes.
-/
theorem cube_add_le_four_mul_sum_cube
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (a + b) ^ 3
      ≤
    4 * (a ^ 3 + b ^ 3) := by
  have h :
      0 ≤ (a + b) * (a - b) ^ 2 :=
    mul_nonneg
      (add_nonneg ha hb)
      (sq_nonneg (a - b))
  nlinarith

/-! ## Splitting the square-gradient frequency factor -/

/--
The Fourier square-gradient factor at `ξ` is controlled by the factors at
`η` and `ξ - η`.
-/
theorem h3FourierGradientSquare_le_two_mul_sum
    (ξ η : H3FourierPoint3) :
    h3FourierGradientSquare ξ
      ≤
    2 *
      (h3FourierGradientSquare η
        + h3FourierGradientSquare (ξ - η)) := by
  have hsymbol
      (i : Fin 3) :
      h3FourierDerivativeSymbol i ξ
        =
      h3FourierDerivativeSymbol i η
        +
      h3FourierDerivativeSymbol i (ξ - η) := by
    unfold h3FourierDerivativeSymbol
    simp [sub_eq_add_neg]
    ring

  have hcoord
      (i : Fin 3) :
      ‖h3FourierDerivativeSymbol i ξ‖ ^ 2
        ≤
      2 *
        (‖h3FourierDerivativeSymbol i η‖ ^ 2
          +
         ‖h3FourierDerivativeSymbol i (ξ - η)‖ ^ 2) := by
    rw [hsymbol i]
    have htri :
        ‖h3FourierDerivativeSymbol i η
            + h3FourierDerivativeSymbol i (ξ - η)‖
          ≤
        ‖h3FourierDerivativeSymbol i η‖
          +
        ‖h3FourierDerivativeSymbol i (ξ - η)‖ :=
      norm_add_le _ _
    have ha :
        0 ≤ ‖h3FourierDerivativeSymbol i η‖ :=
      norm_nonneg _
    have hb :
        0 ≤ ‖h3FourierDerivativeSymbol i (ξ - η)‖ :=
      norm_nonneg _
    have hab :
        0 ≤
          ‖h3FourierDerivativeSymbol i η
            + h3FourierDerivativeSymbol i (ξ - η)‖ :=
      norm_nonneg _
    nlinarith [
      sq_nonneg
        (‖h3FourierDerivativeSymbol i η‖
          - ‖h3FourierDerivativeSymbol i (ξ - η)‖)
    ]

  calc
    h3FourierGradientSquare ξ
        =
      ∑ i : Fin 3,
        ‖h3FourierDerivativeSymbol i ξ‖ ^ 2 := by
          symm
          exact sum_norm_h3FourierDerivativeSymbol_sq ξ
    _ ≤
      ∑ i : Fin 3,
        2 *
          (‖h3FourierDerivativeSymbol i η‖ ^ 2
            +
           ‖h3FourierDerivativeSymbol i (ξ - η)‖ ^ 2) := by
          exact Finset.sum_le_sum fun i _ => hcoord i
    _ =
      2 *
        ((∑ i : Fin 3,
            ‖h3FourierDerivativeSymbol i η‖ ^ 2)
          +
         (∑ i : Fin 3,
            ‖h3FourierDerivativeSymbol i (ξ - η)‖ ^ 2)) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum]
    _ =
      2 *
        (h3FourierGradientSquare η
          + h3FourierGradientSquare (ξ - η)) := by
          rw [
            sum_norm_h3FourierDerivativeSymbol_sq,
            sum_norm_h3FourierDerivativeSymbol_sq
          ]

/--
The square of the gradient factor has the corresponding convolution split.
-/
theorem h3FourierGradientSquare_sq_le_eight_mul_sum_sq
    (ξ η : H3FourierPoint3) :
    (h3FourierGradientSquare ξ) ^ 2
      ≤
    8 *
      ((h3FourierGradientSquare η) ^ 2
        + (h3FourierGradientSquare (ξ - η)) ^ 2) := by
  let q : ℝ := h3FourierGradientSquare ξ
  let a : ℝ := h3FourierGradientSquare η
  let b : ℝ := h3FourierGradientSquare (ξ - η)

  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact h3FourierGradientSquare_nonneg ξ

  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact h3FourierGradientSquare_nonneg η

  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact h3FourierGradientSquare_nonneg (ξ - η)

  have hq :
      q ≤ 2 * (a + b) := by
    dsimp [q, a, b]
    exact h3FourierGradientSquare_le_two_mul_sum ξ η

  have hpow :
      q ^ 2 ≤ (2 * (a + b)) ^ 2 :=
    pow_le_pow_left₀ hq0 hq 2

  calc
    q ^ 2
        ≤
      (2 * (a + b)) ^ 2 :=
        hpow
    _ =
      4 * (a + b) ^ 2 := by
        ring
    _ ≤
      4 * (2 * (a ^ 2 + b ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (sq_add_le_two_mul_sum_sq a b)
          (by norm_num)
    _ =
      8 * (a ^ 2 + b ^ 2) := by
        ring

/--
The cube of the gradient factor has the corresponding convolution split.
-/
theorem h3FourierGradientSquare_cube_le_thirtyTwo_mul_sum_cube
    (ξ η : H3FourierPoint3) :
    (h3FourierGradientSquare ξ) ^ 3
      ≤
    32 *
      ((h3FourierGradientSquare η) ^ 3
        + (h3FourierGradientSquare (ξ - η)) ^ 3) := by
  let q : ℝ := h3FourierGradientSquare ξ
  let a : ℝ := h3FourierGradientSquare η
  let b : ℝ := h3FourierGradientSquare (ξ - η)

  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact h3FourierGradientSquare_nonneg ξ

  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact h3FourierGradientSquare_nonneg η

  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact h3FourierGradientSquare_nonneg (ξ - η)

  have hq :
      q ≤ 2 * (a + b) := by
    dsimp [q, a, b]
    exact h3FourierGradientSquare_le_two_mul_sum ξ η

  have hpow :
      q ^ 3 ≤ (2 * (a + b)) ^ 3 :=
    pow_le_pow_left₀ hq0 hq 3

  calc
    q ^ 3
        ≤
      (2 * (a + b)) ^ 3 :=
        hpow
    _ =
      8 * (a + b) ^ 3 := by
        ring
    _ ≤
      8 * (4 * (a ^ 3 + b ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (cube_add_le_four_mul_sum_cube ha0 hb0)
          (by norm_num)
    _ =
      32 * (a ^ 3 + b ^ 3) := by
        ring

/-! ## Splitting the exact H³ weight -/

/--
The square of the exact H³ weight at `ξ` is bounded by the two convolution
frequency weights.
-/
theorem h3SobolevFrequencyWeightSq_le_thirtyTwo_mul_sum
    (ξ η : H3FourierPoint3) :
    h3SobolevFrequencyWeightSq ξ
      ≤
    32 *
      (h3SobolevFrequencyWeightSq η
        + h3SobolevFrequencyWeightSq (ξ - η)) := by
  have hq :=
    h3FourierGradientSquare_le_two_mul_sum ξ η

  have hq2 :=
    h3FourierGradientSquare_sq_le_eight_mul_sum_sq ξ η

  have hq3 :=
    h3FourierGradientSquare_cube_le_thirtyTwo_mul_sum_cube ξ η

  have ha0 :
      0 ≤ h3FourierGradientSquare η :=
    h3FourierGradientSquare_nonneg η

  have hb0 :
      0 ≤ h3FourierGradientSquare (ξ - η) :=
    h3FourierGradientSquare_nonneg (ξ - η)

  unfold h3SobolevFrequencyWeightSq

  nlinarith [
    sq_nonneg (h3FourierGradientSquare η),
    sq_nonneg (h3FourierGradientSquare (ξ - η))
  ]

/--
Main convolution weight-splitting estimate:

`W₃(ξ) ≤ 8 * (W₃(η) + W₃(ξ - η))`.

The factor eight is deliberately coarse; it avoids any need to optimize
the Sobolev algebra constant.
-/
theorem h3SobolevFrequencyWeight_le_eight_mul_add
    (ξ η : H3FourierPoint3) :
    h3SobolevFrequencyWeight ξ
      ≤
    8 *
      (h3SobolevFrequencyWeight η
        + h3SobolevFrequencyWeight (ξ - η)) := by
  have hSq :=
    h3SobolevFrequencyWeightSq_le_thirtyTwo_mul_sum ξ η

  have hη :
      0 ≤ h3SobolevFrequencyWeight η :=
    (h3SobolevFrequencyWeight_pos η).le

  have hδ :
      0 ≤ h3SobolevFrequencyWeight (ξ - η) :=
    (h3SobolevFrequencyWeight_pos (ξ - η)).le

  have hSqWeight :
      (h3SobolevFrequencyWeight ξ) ^ 2
        ≤
      32 *
        ((h3SobolevFrequencyWeight η) ^ 2
          + (h3SobolevFrequencyWeight (ξ - η)) ^ 2) := by
    rw [
      h3SobolevFrequencyWeight_sq,
      h3SobolevFrequencyWeight_sq,
      h3SobolevFrequencyWeight_sq
    ]
    exact hSq

  have hSquare :
      (h3SobolevFrequencyWeight ξ) ^ 2
        ≤
      (8 *
        (h3SobolevFrequencyWeight η
          + h3SobolevFrequencyWeight (ξ - η))) ^ 2 := by
    calc
      (h3SobolevFrequencyWeight ξ) ^ 2
          ≤
        32 *
          ((h3SobolevFrequencyWeight η) ^ 2
            + (h3SobolevFrequencyWeight (ξ - η)) ^ 2) :=
              hSqWeight
      _ ≤
        64 *
          (h3SobolevFrequencyWeight η
            + h3SobolevFrequencyWeight (ξ - η)) ^ 2 := by
              nlinarith
      _ =
        (8 *
          (h3SobolevFrequencyWeight η
            + h3SobolevFrequencyWeight (ξ - η))) ^ 2 := by
              ring

  have hRight :
      0 ≤
        8 *
          (h3SobolevFrequencyWeight η
            + h3SobolevFrequencyWeight (ξ - η)) := by
    positivity

  have hAbs := (sq_le_sq).mp hSquare

  simpa [
    abs_of_nonneg
      (h3SobolevFrequencyWeight_pos ξ).le,
    abs_of_nonneg hRight
  ] using hAbs

end

end Euclidean
end Bridge
end PrimeTensor
