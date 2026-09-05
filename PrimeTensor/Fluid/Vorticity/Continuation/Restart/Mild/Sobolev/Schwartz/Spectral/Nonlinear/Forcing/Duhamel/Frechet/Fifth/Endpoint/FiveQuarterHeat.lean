import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.ElevenQuarter.Forcing.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SevenQuarterHeat

/-!
# Fifth Fréchet endpoint: residual five-quarter heat multiplier

The selected nonlinear forcing now carries an integrable `11/4` raw Fourier
moment.  Returning to the full fourth state moment therefore leaves precisely

    4 - 11/4 = 5/4

powers for the positive heat lag.

The residual `5/4` heat multiplier is obtained by interpolating the already
closed first and second integer heat moments:

    |ξ|^(5/4)
      =
    (|ξ|^1)^(3/4) (|ξ|^2)^(1/4).

Thus

    |ξ|^(5/4) |H_τ(ξ)|
      ≤
    C₁(ν,τ)^(3/4) C₂(ν,τ)^(1/4),

whose terminal-lag order is `τ^(-5/8)`.  This is strictly integrable at zero.

The final theorem packages the exact estimate needed by the full-fourth source
section:

    m₄(H_τ F)
      ≤
    C_{5/4}(ν,τ) m_{11/4}(F).
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFiveQuarterHeat
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Concrete positive-lag heat coefficient for the residual `5/4` Fourier
weight. -/
noncomputable def h3HeatFiveQuarterMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 1) ^ ((3 : ℝ) / 4)) *
    ((((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 2) ^ ((1 : ℝ) / 4))

theorem h3HeatFiveQuarterMomentCoefficient_nonneg
    {ν τ : ℝ}
    (_hν : 0 ≤ ν)
    (_hτ : 0 ≤ τ) :
    0 ≤ h3HeatFiveQuarterMomentCoefficient ν τ := by
  unfold h3HeatFiveQuarterMomentCoefficient
  positivity

/-- The `5/4` radial weight interpolates the first and second integer
weights. -/
theorem h3FourierFiveQuarterWeight_eq_heatInterpolation
    (ξ : H3FourierPoint3) :
    h3FourierFiveQuarterWeight ξ
      =
    (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
      (‖ξ‖ ^ 2) ^ ((1 : ℝ) / 4) := by
  have hr : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have h2pow :
      ‖ξ‖ ^ (2 : ℝ) = ‖ξ‖ ^ (2 : ℕ) :=
    Real.rpow_natCast ‖ξ‖ 2

  unfold h3FourierFiveQuarterWeight

  calc
    ‖ξ‖ ^ ((5 : ℝ) / 4)
        =
      ‖ξ‖ ^
        (((1 : ℝ) * ((3 : ℝ) / 4)) +
          ((2 : ℝ) * ((1 : ℝ) / 4))) := by
      congr 1
      ring
    _ =
      ‖ξ‖ ^ ((1 : ℝ) * ((3 : ℝ) / 4)) *
        ‖ξ‖ ^ ((2 : ℝ) * ((1 : ℝ) / 4)) := by
      rw [
        Real.rpow_add_of_nonneg
          hr
          (by norm_num : 0 ≤ (1 : ℝ) * ((3 : ℝ) / 4))
          (by norm_num : 0 ≤ (2 : ℝ) * ((1 : ℝ) / 4))
      ]
    _ =
      (‖ξ‖ ^ (1 : ℝ)) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 4) := by
      rw [
        Real.rpow_mul hr,
        Real.rpow_mul hr
      ]
    _ =
      (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ 2) ^ ((1 : ℝ) / 4) := by
      rw [Real.rpow_one, pow_one, h2pow]

/-- Pointwise `5/4` heat smoothing by interpolation between the first and
second integer heat moment bounds. -/
theorem norm_h3HeatFourierSymbol_fiveQuarter_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (ξ : H3FourierPoint3) :
    h3FourierFiveQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatFiveQuarterMomentCoefficient ν τ := by
  let H : ℝ :=
    ‖h3HeatFourierSymbol ν τ ξ‖

  let C : ℝ :=
    (Real.sqrt (ν * (τ / 3)))⁻¹

  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact norm_nonneg _

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have h1 :
      ‖ξ‖ ^ 1 * H
        ≤
      C ^ 1 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 1 (by norm_num) ξ

  have h2 :
      ‖ξ‖ ^ 2 * H
        ≤
      C ^ 2 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 2 (by norm_num) ξ

  have hA0 :
      0 ≤ ‖ξ‖ ^ 1 * H := by
    positivity

  have hB0 :
      0 ≤ ‖ξ‖ ^ 2 * H := by
    positivity

  have hA :
      (‖ξ‖ ^ 1 * H) ^ ((3 : ℝ) / 4)
        ≤
      (C ^ 1) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow
      hA0 h1 (by norm_num)

  have hB :
      (‖ξ‖ ^ 2 * H) ^ ((1 : ℝ) / 4)
        ≤
      (C ^ 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow
      hB0 h2 (by norm_num)

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
    h3FourierFiveQuarterWeight ξ * H
        =
      ((‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
          (‖ξ‖ ^ 2) ^ ((1 : ℝ) / 4)) * H := by
      rw [h3FourierFiveQuarterWeight_eq_heatInterpolation]
    _ =
      ((‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
          (‖ξ‖ ^ 2) ^ ((1 : ℝ) / 4)) *
        (H ^ ((3 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) := by
      rw [hHsplit]
    _ =
      ((‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)) *
        ((‖ξ‖ ^ 2) ^ ((1 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) := by
      ring
    _ =
      (‖ξ‖ ^ 1 * H) ^ ((3 : ℝ) / 4) *
        (‖ξ‖ ^ 2 * H) ^ ((1 : ℝ) / 4) := by
      rw [
        ← Real.mul_rpow
          (pow_nonneg (norm_nonneg ξ) 1)
          hH0,
        ← Real.mul_rpow
          (pow_nonneg (norm_nonneg ξ) 2)
          hH0
      ]
    _ ≤
      (C ^ 1) ^ ((3 : ℝ) / 4) *
        (C ^ 2) ^ ((1 : ℝ) / 4) := by
      exact
        mul_le_mul
          hA hB
          (Real.rpow_nonneg hB0 _)
          (Real.rpow_nonneg (pow_nonneg hC0 1) _)
    _ =
      h3HeatFiveQuarterMomentCoefficient ν τ := by
      dsimp only [C]
      rfl

/-- A full fourth Fourier weight factors as the selected forcing `11/4`
weight times the residual heat `5/4` weight. -/
theorem h3FourierNorm_fourth_eq_elevenQuarter_mul_fiveQuarter
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 4
      =
    h3FourierElevenQuarterWeight ξ *
      h3FourierFiveQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierElevenQuarterWeight
    h3FourierFiveQuarterWeight

  calc
    ‖ξ‖ ^ 4
        =
      ‖ξ‖ ^ (4 : ℝ) := by
        exact (Real.rpow_natCast ‖ξ‖ 4).symm
    _ =
      ‖ξ‖ ^
        (((11 : ℝ) / 4) + ((5 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ ((11 : ℝ) / 4) *
        ‖ξ‖ ^ ((5 : ℝ) / 4) := by
      rw [
        Real.rpow_add_of_nonneg
          hξ0
          (by norm_num : 0 ≤ (11 : ℝ) / 4)
          (by norm_num : 0 ≤ (5 : ℝ) / 4)
      ]

/-- A positive heat lag sends an amplitude with an integrable `11/4` raw
Fourier moment to a complex amplitude with an integrable full-fourth
weight. -/
theorem h3HeatFourierSymbol_fourth_weighted_mul_integrable_of_elevenQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F
        (volume : Measure H3FourierPoint3))
    (hF11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (((‖ξ‖ ^ 4 : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ)))
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν τ

  have hWeightContinuous :
      Continuous (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 4) :=
    continuous_norm.pow 4

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (((‖ξ‖ ^ 4 : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ)))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp hWeightContinuous).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierElevenQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF11.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_fiveQuarter_le
      hν hτ ξ

  have hEleven0 :
      0 ≤ h3FourierElevenQuarterWeight ξ := by
    unfold h3FourierElevenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hFourth0 :
      0 ≤ ‖ξ‖ ^ 4 :=
    pow_nonneg (norm_nonneg ξ) 4

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hFourth0,
    norm_mul,
    h3FourierNorm_fourth_eq_elevenQuarter_mul_fiveQuarter
  ]

  calc
    (h3FourierElevenQuarterWeight ξ *
        h3FourierFiveQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      h3FourierElevenQuarterWeight ξ *
        (h3FourierFiveQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      h3FourierElevenQuarterWeight ξ * C * ‖F ξ‖ := by
      have hScaled :
          h3FourierElevenQuarterWeight ξ *
              (h3FourierFiveQuarterWeight ξ *
                ‖h3HeatFourierSymbol ν τ ξ‖)
            ≤
          h3FourierElevenQuarterWeight ξ * C :=
        mul_le_mul_of_nonneg_left hHeat hEleven0

      exact
        mul_le_mul_of_nonneg_right
          hScaled
          (norm_nonneg (F ξ))
    _ =
      C *
        (h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
      ring

/-- Quantitative full-fourth heat estimate against an amplitude already
carrying an integrable `11/4` Fourier moment. -/
theorem h3HeatFourierSymbol_fourth_norm_integral_le_of_elevenQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F
        (volume : Measure H3FourierPoint3))
    (hF11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatFiveQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν τ

  have hComplex :=
    h3HeatFourierSymbol_fourth_weighted_mul_integrable_of_elevenQuarter
      hν hτ F hF hF11

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hFourth0 :
        ∀ ξ : H3FourierPoint3, 0 ≤ ‖ξ‖ ^ 4 := by
      intro ξ
      exact pow_nonneg (norm_nonneg ξ) 4

    simpa only [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (hFourth0 _)
    ] using hComplex.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierElevenQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF11.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C *
          (h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_fiveQuarter_le
        hν hτ ξ

    have hEleven0 :
        0 ≤ h3FourierElevenQuarterWeight ξ := by
      unfold h3FourierElevenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    rw [
      norm_mul,
      h3FourierNorm_fourth_eq_elevenQuarter_mul_fiveQuarter
    ]

    calc
      (h3FourierElevenQuarterWeight ξ *
          h3FourierFiveQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierElevenQuarterWeight ξ *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierElevenQuarterWeight ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierElevenQuarterWeight ξ *
                (h3FourierFiveQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierElevenQuarterWeight ξ * C :=
          mul_le_mul_of_nonneg_left hHeat hEleven0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C *
          (h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C *
          (h3FourierElevenQuarterWeight ξ * ‖F ξ‖) :=
      hIntegral
    _ =
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ =
      h3HeatFiveQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
