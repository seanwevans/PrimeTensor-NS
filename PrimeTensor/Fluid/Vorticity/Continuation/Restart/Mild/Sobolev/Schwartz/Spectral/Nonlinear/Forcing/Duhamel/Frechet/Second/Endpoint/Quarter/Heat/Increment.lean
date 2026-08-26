import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Semigroup

/-!
# Quarter-Hölder increment bound for the heat multiplier

The quarter-Hölder endpoint cancellation theorem reduces the second Duhamel
derivative to a quantitative time modulus for the selected mild path.

The semigroup contribution is governed by the elementary scalar inequality

    1 - exp(-x) ≤ x^(1/4),    x ≥ 0.

For small `x`, use `1 - exp(-x) ≤ x ≤ x^(1/4)`.
For large `x`, use `1 - exp(-x) ≤ 1 ≤ x^(1/4)`.

Applied to the Fourier heat exponent

    x = (2π)^2 ν h ‖ξ‖^2,

this gives the exact pointwise quarter-Hölder multiplier estimate

    ‖H_h(ξ) - 1‖ ≤ x^(1/4).

Using the heat semigroup law, we then obtain

    ‖H_{a+h}(ξ) - H_a(ξ)‖
      ≤ x^(1/4) ‖H_a(ξ)‖.

This is the pointwise analytic input for the next L²/H³ lifting step.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralQuarterHeatIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Elementary quarter-power envelope for the real heat decrement. -/
theorem h3_one_sub_exp_neg_le_rpow_quarter
    {x : ℝ}
    (hx : 0 ≤ x) :
    1 - Real.exp (-x)
      ≤
    x ^ ((1 : ℝ) / 4) := by
  have hlin :
      1 - Real.exp (-x) ≤ x := by
    have h := Real.one_sub_le_exp_neg x
    linarith

  by_cases hx1 : x ≤ 1
  · have hxrpow :
        x ≤ x ^ ((1 : ℝ) / 4) := by
      exact
        Real.self_le_rpow_of_le_one
          hx hx1 (by norm_num)
    exact le_trans hlin hxrpow
  · have h1x : 1 ≤ x := by
      exact (le_of_lt (lt_of_not_ge hx1))
    have hunit :
        1 - Real.exp (-x) ≤ 1 := by
      have hexp : 0 ≤ Real.exp (-x) :=
        (Real.exp_pos _).le
      linarith
    have h1rpow :
        1 ≤ x ^ ((1 : ℝ) / 4) := by
      exact
        Real.one_le_rpow h1x (by norm_num)
    exact le_trans hunit h1rpow

/-- The one-step heat multiplier differs from the identity by at most the
quarter power of the parabolic frequency-time scale. -/
theorem norm_h3HeatFourierSymbol_sub_one_le_quarter
    {ν h : ℝ}
    (hν : 0 ≤ ν)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν h ξ - 1‖
      ≤
    (((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) ^
      ((1 : ℝ) / 4)) := by
  let x : ℝ :=
    (2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2

  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity

  have hexp_le :
      Real.exp (-x) ≤ 1 := by
    calc
      Real.exp (-x)
          ≤ Real.exp 0 := by
            exact Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
      _ = 1 := Real.exp_zero

  have hq :=
    h3_one_sub_exp_neg_le_rpow_quarter hx

  unfold h3HeatFourierSymbol
  change
    ‖Complex.ofReal
        (Real.exp
          (-((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2))) -
        (1 : ℂ)‖
      ≤
    (((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) ^
      ((1 : ℝ) / 4))

  rw [← Complex.ofReal_one]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]

  change
    |Real.exp (-x) - 1|
      ≤
    x ^ ((1 : ℝ) / 4)

  rw [abs_of_nonpos (sub_nonpos.mpr hexp_le)]
  linarith

/-- Semigroup form of the quarter-Hölder heat increment estimate. -/
theorem norm_h3HeatFourierSymbol_add_sub_le_quarter
    {ν a h : ℝ}
    (hν : 0 ≤ ν)
    (_ha : 0 ≤ a)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖h3HeatFourierSymbol ν (a + h) ξ -
        h3HeatFourierSymbol ν a ξ‖
      ≤
    (((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) ^
        ((1 : ℝ) / 4)) *
      ‖h3HeatFourierSymbol ν a ξ‖ := by
  rw [h3HeatFourierSymbol_add]

  have hFactor :
      h3HeatFourierSymbol ν h ξ *
            h3HeatFourierSymbol ν a ξ -
          h3HeatFourierSymbol ν a ξ
        =
      (h3HeatFourierSymbol ν h ξ - 1) *
        h3HeatFourierSymbol ν a ξ := by
    ring

  rw [hFactor, norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3HeatFourierSymbol_sub_one_le_quarter
        hν hh ξ)
      (norm_nonneg _)

end

end Euclidean
end Bridge
end PrimeTensor
