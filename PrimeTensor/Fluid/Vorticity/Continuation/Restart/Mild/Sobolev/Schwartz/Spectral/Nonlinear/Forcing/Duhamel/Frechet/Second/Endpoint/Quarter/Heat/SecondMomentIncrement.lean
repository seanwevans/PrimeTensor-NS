import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.PositiveLag

/-!
# Positive-lag heat increments after two Fourier moments

The ordinary positive-lag heat increment estimate costs one Fourier frequency:

    |H_{a+h} - H_a|
      <= sqrt((2π)^2 ν h) |ξ| |H_a|.

For the second-Duhamel endpoint problem the scalar profile already carries
`|ξ|^2`.  Multiplying the preceding estimate by those two moments costs three
moments of the positive base heat flow.  The existing `n <= 3` heat smoothing
bound pays for all three:

    |ξ|^2 |H_{a+h} - H_a|
      <= sqrt((2π)^2 ν h) (sqrt(ν(a/3))^-1)^3.

This file records the pointwise multiplier estimate and its Fourier-L1
integrated form for an arbitrary integrable amplitude.  It is the heat-lag
variation half of the continuity estimate for the selected second-moment
profile.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterHeatSecondMomentIncrement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform coefficient for a positive-lag heat-time increment after spending
two Fourier moments. -/
noncomputable def h3HeatPositiveLagSecondMomentIncrementCoefficient
    (ν a h : ℝ) : ℝ :=
  Real.sqrt ((2 * Real.pi) ^ 2 * ν * h) *
    ((Real.sqrt (ν * (a / 3)))⁻¹) ^ 3

theorem h3HeatPositiveLagSecondMomentIncrementCoefficient_nonneg
    {ν a h : ℝ}
    (hν : 0 ≤ ν)
    (ha : 0 ≤ a)
    (hh : 0 ≤ h) :
    0 ≤ h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h := by
  unfold h3HeatPositiveLagSecondMomentIncrementCoefficient
  positivity

/-- Pointwise positive-lag heat increment after paying two additional Fourier
moments. -/
theorem norm_h3HeatFourierSymbol_add_sub_secondMoment_le_positiveLag
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (a + h) ξ -
          h3HeatFourierSymbol ν a ξ‖
      ≤
    h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h := by
  let B : ℝ := (2 * Real.pi) ^ 2 * ν * h

  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hStep :=
    norm_h3HeatFourierSymbol_add_sub_le_sqrt
      hν.le ha.le hh ξ

  have hMoment :=
    h3HeatFourierMomentMultiplier_le_three
      hν ha 3 (by norm_num) ξ

  have hSqrt :
      Real.sqrt (B * ‖ξ‖ ^ 2)
        = Real.sqrt B * ‖ξ‖ := by
    rw [Real.sqrt_mul hB]
    rw [Real.sqrt_sq (norm_nonneg ξ)]

  calc
    ‖ξ‖ ^ 2 *
        ‖h3HeatFourierSymbol ν (a + h) ξ -
          h3HeatFourierSymbol ν a ξ‖
        ≤
      ‖ξ‖ ^ 2 *
        (Real.sqrt
            ((2 * Real.pi) ^ 2 * ν * h * ‖ξ‖ ^ 2) *
          ‖h3HeatFourierSymbol ν a ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          hStep
          (sq_nonneg ‖ξ‖)
    _ =
      Real.sqrt B *
        (‖ξ‖ ^ 3 * ‖h3HeatFourierSymbol ν a ξ‖) := by
      change
        ‖ξ‖ ^ 2 *
            (Real.sqrt (B * ‖ξ‖ ^ 2) *
              ‖h3HeatFourierSymbol ν a ξ‖)
          =
        Real.sqrt B *
          (‖ξ‖ ^ 3 * ‖h3HeatFourierSymbol ν a ξ‖)
      rw [hSqrt]
      ring
    _ ≤
      Real.sqrt B *
        ((Real.sqrt (ν * (a / 3)))⁻¹) ^ 3 := by
      exact
        mul_le_mul_of_nonneg_left
          hMoment
          (Real.sqrt_nonneg B)
    _ =
      h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h := by
      rfl

/-- Fourier-L1 version of the positive-lag heat increment after two Fourier
moments. -/
theorem h3HeatFourierSymbol_add_sub_secondMoment_norm_integral_le_positiveLag
    {ν a h : ℝ}
    (hν : 0 < ν)
    (ha : 0 < a)
    (hh : 0 ≤ h)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖(h3HeatFourierSymbol ν (a + h) ξ -
              h3HeatFourierSymbol ν a ξ) * F ξ‖)
      ≤
    h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h *
      (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h

  have hC : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatPositiveLagSecondMomentIncrementCoefficient_nonneg
        hν.le ha.le hh

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖(h3HeatFourierSymbol ν (a + h) ξ -
                h3HeatFourierSymbol ν a ξ) * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        (((continuous_h3HeatFourierSymbol ν (a + h)).sub
            (continuous_h3HeatFourierSymbol ν a)).aestronglyMeasurable.mul
          hF.aestronglyMeasurable).norm

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 => C * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF.norm.const_mul C

  have hTargetInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖(h3HeatFourierSymbol ν (a + h) ξ -
                h3HeatFourierSymbol ν a ξ) * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajorantInt.mono' hTargetMeas ?_
    filter_upwards with ξ
    have hPoint :=
      norm_h3HeatFourierSymbol_add_sub_secondMoment_le_positiveLag
        hν ha hh ξ
    have hTargetNonneg :
        0 ≤
          ‖ξ‖ ^ 2 *
            ‖(h3HeatFourierSymbol ν (a + h) ξ -
                h3HeatFourierSymbol ν a ξ) * F ξ‖ := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
    rw [norm_mul]
    calc
      ‖ξ‖ ^ 2 *
          (‖h3HeatFourierSymbol ν (a + h) ξ -
              h3HeatFourierSymbol ν a ξ‖ * ‖F ξ‖)
          =
        (‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (a + h) ξ -
            h3HeatFourierSymbol ν a ξ‖) * ‖F ξ‖ := by
        ring
      _ ≤ C * ‖F ξ‖ := by
        exact
          mul_le_mul_of_nonneg_right
            hPoint
            (norm_nonneg (F ξ))

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖(h3HeatFourierSymbol ν (a + h) ξ -
              h3HeatFourierSymbol ν a ξ) * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, C * ‖F ξ‖ := by
      refine integral_mono_ae hTargetInt hMajorantInt ?_
      filter_upwards with ξ
      have hPoint :=
        norm_h3HeatFourierSymbol_add_sub_secondMoment_le_positiveLag
          hν ha hh ξ
      rw [norm_mul]
      calc
        ‖ξ‖ ^ 2 *
            (‖h3HeatFourierSymbol ν (a + h) ξ -
                h3HeatFourierSymbol ν a ξ‖ * ‖F ξ‖)
            =
          (‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (a + h) ξ -
              h3HeatFourierSymbol ν a ξ‖) * ‖F ξ‖ := by
          ring
        _ ≤ C * ‖F ξ‖ := by
          exact
            mul_le_mul_of_nonneg_right
              hPoint
              (norm_nonneg (F ξ))
    _ = C * (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
      rw [integral_const_mul]
    _ =
      h3HeatPositiveLagSecondMomentIncrementCoefficient ν a h *
        (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
      rfl

end

end Euclidean
end Bridge
end PrimeTensor
