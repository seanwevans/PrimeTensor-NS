import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Velocity.Kernel

/-!
# Fin-indexed Fourier Leray symbol

The velocity Picard operator requires the Fourier Leray projector

    P(ξ) = I - ξ ⊗ ξ / |ξ|².

Rather than reopen the `Axis Depth.three ↔ Fin 3` coordinate bridge, define the
same rank-one projector from the already-verified Fourier derivative symbols

    dᵢ(ξ) = 2π i ξᵢ.

Then

    dᵢ conj(dⱼ) / Σₖ |dₖ|²
      = ξᵢ ξⱼ / |ξ|²

away from zero frequency, because the common `2π` factors and the imaginary
units cancel.  At zero frequency the rank-one term is defined to be zero, so
the Leray symbol is the identity there.

For the finite-product sup norm used by the restart spectral state, a coarse
entrywise bound is sufficient:

    |Rᵢⱼ(ξ)| ≤ 1,
    |Pᵢⱼ(ξ)| ≤ 2.

The next rung lifts this bounded measurable matrix multiplier to the weighted
spectral `L²` vector state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Kronecker delta as a complex scalar. -/
def h3LerayDelta
    (i j : Fin 3) : ℂ :=
  if i = j then 1 else 0

/-- The finite-dimensional delta entry has norm at most one. -/
theorem norm_h3LerayDelta_le_one
    (i j : Fin 3) :
    ‖h3LerayDelta i j‖ ≤ 1 := by
  by_cases hij : i = j
  · simp [h3LerayDelta, hij]
  · simp [h3LerayDelta, hij]

/--
Rank-one frequency-direction coefficient.

At zero frequency the denominator vanishes and the coefficient is defined to
be zero.
-/
noncomputable def h3LerayRankOneCoefficient
    (ξ : H3FourierPoint3)
    (i j : Fin 3) : ℂ :=
  if hq : h3FourierGradientSquare ξ = 0 then
    0
  else
    h3FourierDerivativeSymbol i ξ *
        star (h3FourierDerivativeSymbol j ξ) /
      (h3FourierGradientSquare ξ : ℂ)

/--
The numerator of the rank-one coefficient is bounded by the total gradient
square.
-/
theorem norm_h3LerayRankOneNumerator_le
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    ‖h3FourierDerivativeSymbol i ξ *
        star (h3FourierDerivativeSymbol j ξ)‖
      ≤
    h3FourierGradientSquare ξ := by
  have hi :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ
  have hj :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ
  have hmag :
      0 ≤ h3FourierGradientMagnitude ξ :=
    h3FourierGradientMagnitude_nonneg ξ

  calc
    ‖h3FourierDerivativeSymbol i ξ *
        star (h3FourierDerivativeSymbol j ξ)‖
        =
      ‖h3FourierDerivativeSymbol i ξ‖ *
        ‖h3FourierDerivativeSymbol j ξ‖ := by
          rw [norm_mul, norm_star]
    _ ≤
      h3FourierGradientMagnitude ξ *
        h3FourierGradientMagnitude ξ := by
          exact
            mul_le_mul
              hi hj
              (norm_nonneg _)
              hmag
    _ =
      (h3FourierGradientMagnitude ξ) ^ 2 := by
          ring
    _ =
      h3FourierGradientSquare ξ :=
      h3FourierGradientMagnitude_sq ξ

/-- Every rank-one Leray coefficient has norm at most one. -/
theorem norm_h3LerayRankOneCoefficient_le_one
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    ‖h3LerayRankOneCoefficient ξ i j‖ ≤ 1 := by
  by_cases hq : h3FourierGradientSquare ξ = 0
  · simp [h3LerayRankOneCoefficient, hq]
  · have hqnonneg :
        0 ≤ h3FourierGradientSquare ξ :=
      h3FourierGradientSquare_nonneg ξ

    have hqpos :
        0 < h3FourierGradientSquare ξ :=
      lt_of_le_of_ne
        hqnonneg
        (Ne.symm hq)

    have hnum :
        ‖h3FourierDerivativeSymbol i ξ *
            star (h3FourierDerivativeSymbol j ξ)‖
          ≤
        h3FourierGradientSquare ξ :=
      norm_h3LerayRankOneNumerator_le ξ i j

    rw [h3LerayRankOneCoefficient, dif_neg hq]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hqnonneg]
    rw [div_le_iff₀ hqpos]
    simpa using hnum

/-- Matrix entry of the Fourier Leray projector. -/
noncomputable def h3LerayCoefficient
    (ξ : H3FourierPoint3)
    (i j : Fin 3) : ℂ :=
  h3LerayDelta i j -
    h3LerayRankOneCoefficient ξ i j

/-- Every Leray matrix entry has the coarse uniform bound `2`. -/
theorem norm_h3LerayCoefficient_le_two
    (ξ : H3FourierPoint3)
    (i j : Fin 3) :
    ‖h3LerayCoefficient ξ i j‖ ≤ 2 := by
  calc
    ‖h3LerayCoefficient ξ i j‖
        ≤
      ‖h3LerayDelta i j‖ +
        ‖h3LerayRankOneCoefficient ξ i j‖ := by
          simpa [h3LerayCoefficient] using
            norm_sub_le
              (h3LerayDelta i j)
              (h3LerayRankOneCoefficient ξ i j)
    _ ≤ 1 + 1 :=
      add_le_add
        (norm_h3LerayDelta_le_one i j)
        (norm_h3LerayRankOneCoefficient_le_one ξ i j)
    _ = 2 := by norm_num

/-- At zero gradient frequency the Leray symbol is exactly the identity matrix. -/
theorem h3LerayCoefficient_of_gradientSquare_eq_zero
    {ξ : H3FourierPoint3}
    (hξ : h3FourierGradientSquare ξ = 0)
    (i j : Fin 3) :
    h3LerayCoefficient ξ i j =
      h3LerayDelta i j := by
  simp [h3LerayCoefficient,
    h3LerayRankOneCoefficient, hξ]

end

end Euclidean
end Bridge
end PrimeTensor
