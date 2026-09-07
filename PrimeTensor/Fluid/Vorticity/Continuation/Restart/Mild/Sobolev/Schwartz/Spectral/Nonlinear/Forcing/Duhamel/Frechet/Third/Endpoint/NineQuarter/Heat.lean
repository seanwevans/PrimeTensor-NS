import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Heat.Second.Moment.Increment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.Frozen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Nine-quarter Fourier heat moment

The third-Duhamel endpoint does not need a full third Fourier moment of the
selected state immediately.

The quarter-Hölder source-time cancellation permits any gain strictly below
one half moment beyond the already-closed second moment.  We choose the
concrete exponent

    2 + 1/4 = 9/4.

This file isolates the heat-multiplier interpolation needed for that
fractional bootstrap.

The exact real-power identity

    |ξ|^(9/4)
      =
    (|ξ|^2)^(3/4) (|ξ|^3)^(1/4)

allows the existing second- and third-integer heat moment estimates to be
interpolated pointwise:

    |ξ|^(9/4) |H_τ(ξ)|
      <=
    C₂(ν,τ)^(3/4) C₃(ν,τ)^(1/4).

An integrated version against an arbitrary Fourier-L¹ amplitude is also
recorded.  The next checkpoint will combine this with the selected
quarter-Hölder forcing difference and reduce the terminal singularity to the
integrable power `(t-s)^(-7/8)`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdEndpointNineQuarterHeat
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The concrete fractional Fourier weight used for the first C³ bootstrap
gain beyond two moments. -/
noncomputable def h3FourierNineQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((9 : ℝ) / 4)

/-- The `9/4` weight is the geometric interpolation of the second and third
integer Fourier weights. -/
theorem h3FourierNineQuarterWeight_eq_interpolation
    (ξ : H3FourierPoint3) :
    h3FourierNineQuarterWeight ξ
      =
    (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
      (‖ξ‖ ^ 3) ^ ((1 : ℝ) / 4) := by
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  have h2pow :
      ‖ξ‖ ^ (2 : ℝ) = ‖ξ‖ ^ (2 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 2

  have h3pow :
      ‖ξ‖ ^ (3 : ℝ) = ‖ξ‖ ^ (3 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 3

  unfold h3FourierNineQuarterWeight

  calc
    ‖ξ‖ ^ ((9 : ℝ) / 4)
        =
      ‖ξ‖ ^
        (((2 : ℝ) * ((3 : ℝ) / 4)) +
          ((3 : ℝ) * ((1 : ℝ) / 4))) := by
      congr 1
      ring
    _ =
      ‖ξ‖ ^ ((2 : ℝ) * ((3 : ℝ) / 4)) *
        ‖ξ‖ ^ ((3 : ℝ) * ((1 : ℝ) / 4)) := by
      rw [
        Real.rpow_add_of_nonneg
          hr
          (by norm_num : 0 ≤ (2 : ℝ) * ((3 : ℝ) / 4))
          (by norm_num : 0 ≤ (3 : ℝ) * ((1 : ℝ) / 4))
      ]
    _ =
      (‖ξ‖ ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ (3 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [
        Real.rpow_mul hr,
        Real.rpow_mul hr
      ]
    _ =
      (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ 3) ^ ((1 : ℝ) / 4) := by
      rw [h2pow, h3pow]

/-- Interpolated positive-lag heat coefficient for the `9/4` Fourier moment. -/
noncomputable def h3HeatNineQuarterMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2) ^ ((3 : ℝ) / 4)) *
    ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 3) ^ ((1 : ℝ) / 4))

theorem h3HeatNineQuarterMomentCoefficient_nonneg
    {ν τ : ℝ}
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ) :
    0 ≤ h3HeatNineQuarterMomentCoefficient ν τ := by
  unfold h3HeatNineQuarterMomentCoefficient
  positivity

/-- Pointwise `9/4` heat smoothing obtained by geometric interpolation between
the already-closed second and third integer moment estimates. -/
theorem norm_h3HeatFourierSymbol_nineQuarter_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (ξ : H3FourierPoint3) :
    h3FourierNineQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatNineQuarterMomentCoefficient ν τ := by
  let H : ℝ := ‖h3HeatFourierSymbol ν τ ξ‖
  let C : ℝ := (Real.sqrt (ν * (τ / 3)))⁻¹

  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact norm_nonneg _

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have h2 :
      ‖ξ‖ ^ 2 * H ≤ C ^ 2 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 2 (by norm_num) ξ

  have h3 :
      ‖ξ‖ ^ 3 * H ≤ C ^ 3 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 3 (by norm_num) ξ

  have hA0 : 0 ≤ ‖ξ‖ ^ 2 * H := by
    positivity

  have hB0 : 0 ≤ ‖ξ‖ ^ 3 * H := by
    positivity

  have hA :
      (‖ξ‖ ^ 2 * H) ^ ((3 : ℝ) / 4)
        ≤
      (C ^ 2) ^ ((3 : ℝ) / 4) := by
    exact
      Real.rpow_le_rpow
        hA0 h2 (by norm_num)

  have hB :
      (‖ξ‖ ^ 3 * H) ^ ((1 : ℝ) / 4)
        ≤
      (C ^ 3) ^ ((1 : ℝ) / 4) := by
    exact
      Real.rpow_le_rpow
        hB0 h3 (by norm_num)

  have hHsplit :
      H ^ ((3 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)
        =
      H := by
    rw [
      ← Real.rpow_add_of_nonneg
        hH0
        (by norm_num : 0 ≤ (3 : ℝ) / 4)
        (by norm_num : 0 ≤ (1 : ℝ) / 4)
    ]
    norm_num

  calc
    h3FourierNineQuarterWeight ξ * H
        =
      ((‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
          (‖ξ‖ ^ 3) ^ ((1 : ℝ) / 4)) * H := by
      rw [h3FourierNineQuarterWeight_eq_interpolation]
    _ =
      ((‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
          (‖ξ‖ ^ 3) ^ ((1 : ℝ) / 4)) *
        (H ^ ((3 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) := by
      rw [hHsplit]
    _ =
      ((‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)) *
        ((‖ξ‖ ^ 3) ^ ((1 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) := by
      ring
    _ =
      (‖ξ‖ ^ 2 * H) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ 3 * H) ^ ((1 : ℝ) / 4) := by
      rw [
        ← Real.mul_rpow
          (sq_nonneg ‖ξ‖)
          hH0,
        ← Real.mul_rpow
          (pow_nonneg (norm_nonneg ξ) 3)
          hH0
      ]
    _ ≤
      (C ^ 2) ^ ((3 : ℝ) / 4) *
        (C ^ 3) ^ ((1 : ℝ) / 4) := by
      exact
        mul_le_mul
          hA hB
          (Real.rpow_nonneg hB0 _)
          (Real.rpow_nonneg (pow_nonneg hC0 2) _)
    _ =
      h3HeatNineQuarterMomentCoefficient ν τ := by
      dsimp only [C]
      rfl

/-- Fourier-L¹ integrated `9/4` heat smoothing bound for an arbitrary
integrable complex amplitude. -/
theorem h3HeatFourierSymbol_nineQuarter_norm_integral_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatNineQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
  let C : ℝ := h3HeatNineQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatNineQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hWeightContinuous :
      Continuous h3FourierNineQuarterWeight := by
    unfold h3FourierNineQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      hWeightContinuous.aestronglyMeasurable.mul
        ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
          hF.aestronglyMeasurable).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF.norm.const_mul C

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hTargetMeas ?_
    filter_upwards with ξ

    have hPoint :=
      norm_h3HeatFourierSymbol_nineQuarter_le
        hν hτ ξ

    have hTarget0 :
        0 ≤
          h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ := by
      unfold h3FourierNineQuarterWeight
      positivity

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg hTarget0,
      norm_mul
    ]

    calc
      h3FourierNineQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        (h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖ := by
        ring
      _ ≤ C * ‖F ξ‖ :=
        mul_le_mul_of_nonneg_right
          hPoint
          (norm_nonneg _)

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C * ‖F ξ‖ := by
      refine integral_mono_ae hTarget hMajor ?_
      filter_upwards with ξ

      have hPoint :=
        norm_h3HeatFourierSymbol_nineQuarter_le
          hν hτ ξ

      rw [norm_mul]

      calc
        h3FourierNineQuarterWeight ξ *
            (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
            =
          (h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖ := by
          ring
        _ ≤ C * ‖F ξ‖ :=
          mul_le_mul_of_nonneg_right
            hPoint
            (norm_nonneg _)
    _ =
      C * (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
      rw [integral_const_mul]
    _ =
      h3HeatNineQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3, ‖F ξ‖) := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
