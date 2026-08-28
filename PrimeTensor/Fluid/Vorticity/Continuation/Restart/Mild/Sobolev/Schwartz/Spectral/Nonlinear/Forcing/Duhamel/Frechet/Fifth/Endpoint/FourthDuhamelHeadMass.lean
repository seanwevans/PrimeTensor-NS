import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FourthNamedTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterDuhamelHeadMass

/-!
# Fifth Fréchet endpoint: quantitative full-fourth Duhamel midpoint head

The terminal half now has a quantitative named full-fourth moment.

For the midpoint head, the shorter-time complete selected Duhamel state at
`t/2` already has a cubic raw Fourier moment.  Only one additional heat power
is required:

    4 = 3 + 1.

The existing integer heat multiplier estimate gives

    |ξ| |H_τ(ξ)|
      ≤
    (sqrt(ν (τ/3)))⁻¹.

Therefore

    m₄(H_{t/2} D(t/2))
      ≤
    C₁(ν,t/2) m₃(D(t/2)).

This file transfers that estimate to the quotient-safe named selected midpoint
head used by the full Duhamel decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFourthDuhamelHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-lag heat coefficient for one full radial Fourier power. -/
noncomputable def h3HeatOneMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  ((Real.sqrt (ν * (τ / 3)))⁻¹) ^ (1 : ℕ)

theorem h3HeatOneMomentCoefficient_nonneg
    {ν τ : ℝ}
    (_hν : 0 ≤ ν)
    (_hτ : 0 ≤ τ) :
    0 ≤ h3HeatOneMomentCoefficient ν τ := by
  unfold h3HeatOneMomentCoefficient
  positivity

/-- Pointwise first heat-moment multiplier bound. -/
theorem norm_h3HeatFourierSymbol_oneMoment_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (ξ : H3FourierPoint3) :
    ‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatOneMomentCoefficient ν τ := by
  have h :=
    h3HeatFourierMomentMultiplier_le_three
      hν hτ 1 (by norm_num) ξ

  unfold h3HeatOneMomentCoefficient
  simpa only [pow_one] using h

/-- The fourth radial power factors as the cubic source weight times one
residual radial power. -/
theorem h3FourierNorm_fourth_eq_cubed_mul_one
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 4
      =
    ‖ξ‖ ^ 3 * ‖ξ‖ := by
  ring

/-- Positive heat lag upgrades a cubic raw Fourier moment to a full fourth
moment. -/
theorem h3HeatFourierSymbol_fourth_norm_integrable_of_third
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatOneMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatOneMomentCoefficient_nonneg
        hν.le hτ.le

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable F)).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_oneMoment_le
      hν hτ ξ

  have hCube0 :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ :=
    mul_nonneg
      (pow_nonneg (norm_nonneg ξ) 4)
      (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) :=
    mul_nonneg hC0
      (mul_nonneg hCube0 (norm_nonneg _))

  have hBound :
      ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
        ≤
      C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
    rw [
      h3FourierNorm_fourth_eq_cubed_mul_one,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 3 * ‖ξ‖) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 3 *
          (‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 3 *
                (‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hCube0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Quantitative positive-lag heat smoothing from cubic raw Fourier mass to a
full fourth moment. -/
theorem h3HeatFourierSymbol_fourth_norm_integral_le_of_third
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatOneMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatOneMomentCoefficient ν τ

  have hTarget :=
    h3HeatFourierSymbol_fourth_norm_integrable_of_third
      hν hτ F hF3

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_oneMoment_le
        hν hτ ξ

    have hCube0 :
        0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3

    rw [
      h3FourierNorm_fourth_eq_cubed_mul_one,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 3 * ‖ξ‖) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 3 *
          (‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 3 *
                (‖ξ‖ * ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hCube0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  dsimp only [C] at hIntegral ⊢

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatOneMomentCoefficient ν τ *
          (‖ξ‖ ^ 3 * ‖F ξ‖) :=
      hIntegral
    _ =
      h3HeatOneMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖F ξ‖) := by
      rw [integral_const_mul]

/-- Explicit full-fourth raw Fourier mass envelope for one selected midpoint
head coordinate. -/
noncomputable def h3SelectedDuhamelHeadFourthMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatOneMomentCoefficient ν (t / 2) *
    h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2)

/-- The named selected positive-lag Duhamel head has an integrable full fourth
raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fourthMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 4 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalfR :
      t / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) htR

  have hD3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeat :=
    h3HeatFourierSymbol_fourth_norm_integrable_of_third
      hν hhalf0 D hD3

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  refine hHeat.congr ?_
  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Quantitative full-fourth raw Fourier mass of the named selected midpoint
head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fourthMomentMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadFourthMomentEnvelope ν A t := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalfR :
      t / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) htR

  have hD3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeatBound :=
    h3HeatFourierSymbol_fourth_norm_integral_le_of_third
      hν hhalf0 D hD3

  have hD3Bound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integral_le
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hCoeff0 :
      0 ≤ h3HeatOneMomentCoefficient ν (t / 2) :=
    h3HeatOneMomentCoefficient_nonneg
      hν.le hhalf0.le

  unfold h3SelectedDuhamelHeadFourthMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ :=
      hIntegralEq
    _ ≤
      h3HeatOneMomentCoefficient ν (t / 2) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖) :=
      hHeatBound
    _ ≤
      h3HeatOneMomentCoefficient ν (t / 2) *
        h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2) :=
      mul_le_mul_of_nonneg_left hD3Bound hCoeff0

end
end Euclidean
end Bridge
end PrimeTensor
