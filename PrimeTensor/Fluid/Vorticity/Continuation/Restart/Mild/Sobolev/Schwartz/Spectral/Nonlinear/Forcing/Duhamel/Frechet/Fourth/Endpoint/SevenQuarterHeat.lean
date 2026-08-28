import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirteenQuarterFrozen
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterHeat

/-!
# Seven-quarter heat multiplier for the next subcritical endpoint

The selected nonlinear forcing now has an integrable `5/4` raw Fourier moment.
For a full third Fourier moment of the Duhamel integrand, the remaining heat
weight is therefore

    3 - 5/4 = 7/4.

This file isolates that heat factor.

The `7/4` heat multiplier is obtained by geometric interpolation between the
already-closed first and second integer heat moments:

    |ξ|^(7/4)
      =
    (|ξ|^1)^(1/4) (|ξ|^2)^(3/4).

Hence

    |ξ|^(7/4) |H_τ(ξ)|
      ≤
    C₁(ν,τ)^(1/4) C₂(ν,τ)^(3/4),

whose lag singularity is `τ^(-7/8)`.  That exponent is integrable at the
terminal endpoint.

The final theorem packages the form needed by the forcing variation layer:
a `5/4`-weighted Fourier-L¹ amplitude becomes an integrable full-third-moment
amplitude after any positive heat lag.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSevenQuarterHeat
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Residual heat weight after a `5/4` forcing moment is inserted into a full
third Fourier moment. -/
noncomputable def h3FourierSevenQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((7 : ℝ) / 4)

/-- The `7/4` radial weight interpolates the first and second integer weights. -/
theorem h3FourierSevenQuarterWeight_eq_interpolation
    (ξ : H3FourierPoint3) :
    h3FourierSevenQuarterWeight ξ
      =
    (‖ξ‖ ^ 1) ^ ((1 : ℝ) / 4) *
      (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) := by
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  have h2pow :
      ‖ξ‖ ^ (2 : ℝ) = ‖ξ‖ ^ (2 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 2

  unfold h3FourierSevenQuarterWeight

  calc
    ‖ξ‖ ^ ((7 : ℝ) / 4)
        =
      ‖ξ‖ ^
        (((1 : ℝ) * ((1 : ℝ) / 4)) +
          ((2 : ℝ) * ((3 : ℝ) / 4))) := by
      congr 1
      ring
    _ =
      ‖ξ‖ ^ ((1 : ℝ) * ((1 : ℝ) / 4)) *
        ‖ξ‖ ^ ((2 : ℝ) * ((3 : ℝ) / 4)) := by
      rw [
        Real.rpow_add_of_nonneg
          hr
          (by norm_num : 0 ≤ (1 : ℝ) * ((1 : ℝ) / 4))
          (by norm_num : 0 ≤ (2 : ℝ) * ((3 : ℝ) / 4))
      ]
    _ =
      (‖ξ‖ ^ (1 : ℝ)) ^ ((1 : ℝ) / 4) *
        (‖ξ‖ ^ (2 : ℝ)) ^ ((3 : ℝ) / 4) := by
      rw [
        Real.rpow_mul hr,
        Real.rpow_mul hr
      ]
    _ =
      (‖ξ‖ ^ 1) ^ ((1 : ℝ) / 4) *
        (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) := by
      rw [Real.rpow_one, pow_one, h2pow]

/-- Concrete positive-lag heat coefficient for the `7/4` Fourier weight. -/
noncomputable def h3HeatSevenQuarterMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 1) ^ ((1 : ℝ) / 4)) *
    ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2) ^ ((3 : ℝ) / 4))

theorem h3HeatSevenQuarterMomentCoefficient_nonneg
    {ν τ : ℝ}
    (hν : 0 ≤ ν)
    (hτ : 0 ≤ τ) :
    0 ≤ h3HeatSevenQuarterMomentCoefficient ν τ := by
  unfold h3HeatSevenQuarterMomentCoefficient
  positivity

/-- Pointwise `7/4` heat smoothing by interpolation between the first and
second integer heat moment bounds. -/
theorem norm_h3HeatFourierSymbol_sevenQuarter_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (ξ : H3FourierPoint3) :
    h3FourierSevenQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatSevenQuarterMomentCoefficient ν τ := by
  let H : ℝ := ‖h3HeatFourierSymbol ν τ ξ‖
  let C : ℝ := (Real.sqrt (ν * (τ / 3)))⁻¹

  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact norm_nonneg _

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have h1 :
      ‖ξ‖ ^ 1 * H ≤ C ^ 1 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 1 (by norm_num) ξ

  have h2 :
      ‖ξ‖ ^ 2 * H ≤ C ^ 2 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 2 (by norm_num) ξ

  have hA0 : 0 ≤ ‖ξ‖ ^ 1 * H := by
    positivity

  have hB0 : 0 ≤ ‖ξ‖ ^ 2 * H := by
    positivity

  have hA :
      (‖ξ‖ ^ 1 * H) ^ ((1 : ℝ) / 4)
        ≤
      (C ^ 1) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hA0 h1 (by norm_num)

  have hB :
      (‖ξ‖ ^ 2 * H) ^ ((3 : ℝ) / 4)
        ≤
      (C ^ 2) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hB0 h2 (by norm_num)

  have hHsplit :
      H ^ ((1 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)
        =
      H := by
    rw [
      ← Real.rpow_add_of_nonneg
        hH0
        (by norm_num : 0 ≤ (1 : ℝ) / 4)
        (by norm_num : 0 ≤ (3 : ℝ) / 4)
    ]
    norm_num

  calc
    h3FourierSevenQuarterWeight ξ * H
        =
      ((‖ξ‖ ^ 1) ^ ((1 : ℝ) / 4) *
          (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4)) * H := by
      rw [h3FourierSevenQuarterWeight_eq_interpolation]
    _ =
      ((‖ξ‖ ^ 1) ^ ((1 : ℝ) / 4) *
          (‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4)) *
        (H ^ ((1 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)) := by
      rw [hHsplit]
    _ =
      ((‖ξ‖ ^ 1) ^ ((1 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) *
        ((‖ξ‖ ^ 2) ^ ((3 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)) := by
      ring
    _ =
      (‖ξ‖ ^ 1 * H) ^ ((1 : ℝ) / 4) *
        (‖ξ‖ ^ 2 * H) ^ ((3 : ℝ) / 4) := by
      rw [
        ← Real.mul_rpow
          (pow_nonneg (norm_nonneg ξ) 1)
          hH0,
        ← Real.mul_rpow
          (pow_nonneg (norm_nonneg ξ) 2)
          hH0
      ]
    _ ≤
      (C ^ 1) ^ ((1 : ℝ) / 4) *
        (C ^ 2) ^ ((3 : ℝ) / 4) := by
      exact
        mul_le_mul
          hA hB
          (Real.rpow_nonneg hB0 _)
          (Real.rpow_nonneg (pow_nonneg hC0 1) _)
    _ =
      h3HeatSevenQuarterMomentCoefficient ν τ := by
      dsimp only [C]
      rfl

/-- A full third Fourier weight factors as the selected forcing `5/4` weight
times the residual heat `7/4` weight. -/
theorem h3FourierNorm_cubed_eq_fiveQuarter_mul_sevenQuarter
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 3
      =
    h3FourierFiveQuarterWeight ξ *
      h3FourierSevenQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  unfold h3FourierFiveQuarterWeight
  unfold h3FourierSevenQuarterWeight

  calc
    ‖ξ‖ ^ 3
        =
      ‖ξ‖ ^ (3 : ℝ) := by
        exact (Real.rpow_natCast ‖ξ‖ 3).symm
    _ =
      ‖ξ‖ ^ (((5 : ℝ) / 4) + ((7 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ ((5 : ℝ) / 4) *
        ‖ξ‖ ^ ((7 : ℝ) / 4) := by
      rw [
        Real.rpow_add_of_nonneg
          hξ0
          (by norm_num : 0 ≤ (5 : ℝ) / 4)
          (by norm_num : 0 ≤ (7 : ℝ) / 4)
      ]

/-- Integrated third-moment heat bound against an amplitude already carrying an
integrable `5/4` Fourier moment. -/
theorem h3HeatFourierSymbol_third_norm_integral_le_of_fiveQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F (volume : Measure H3FourierPoint3))
    (hF5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatSevenQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
  let C : ℝ := h3HeatSevenQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 3).aestronglyMeasurable).mul
        ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
          hF.aestronglyMeasurable).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierFiveQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF5.const_mul C

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hMajor.mono' hTargetMeas ?_
    filter_upwards with ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_sevenQuarter_le
        hν hτ ξ

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hTarget0 :
        0 ≤
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ := by
      positivity

    rw [
      Real.norm_eq_abs,
      abs_of_nonneg hTarget0,
      norm_mul,
      h3FourierNorm_cubed_eq_fiveQuarter_mul_sevenQuarter
    ]

    calc
      (h3FourierFiveQuarterWeight ξ *
          h3FourierSevenQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierFiveQuarterWeight ξ *
          (h3FourierSevenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖ := by
        ring
      _ =
        h3FourierFiveQuarterWeight ξ *
          ((h3FourierSevenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖) := by
        ring
      _ ≤
        h3FourierFiveQuarterWeight ξ *
          (C * ‖F ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hHeat (norm_nonneg (F ξ)))
            hFive0
      _ =
        C *
          (h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
        ring

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C *
          (h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
      refine integral_mono_ae hTarget hMajor ?_
      filter_upwards with ξ

      have hHeat :=
        norm_h3HeatFourierSymbol_sevenQuarter_le
          hν hτ ξ

      have hFive0 :
          0 ≤ h3FourierFiveQuarterWeight ξ := by
        unfold h3FourierFiveQuarterWeight
        exact Real.rpow_nonneg (norm_nonneg ξ) _

      rw [
        norm_mul,
        h3FourierNorm_cubed_eq_fiveQuarter_mul_sevenQuarter
      ]

      calc
        (h3FourierFiveQuarterWeight ξ *
            h3FourierSevenQuarterWeight ξ) *
            (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
            =
          h3FourierFiveQuarterWeight ξ *
            (h3FourierSevenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖ := by
          ring
        _ =
          h3FourierFiveQuarterWeight ξ *
            ((h3FourierSevenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖) := by
          ring
        _ ≤
          h3FourierFiveQuarterWeight ξ *
            (C * ‖F ξ‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hHeat (norm_nonneg (F ξ)))
              hFive0
        _ =
          C *
            (h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
          ring
    _ =
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ =
      h3HeatSevenQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
