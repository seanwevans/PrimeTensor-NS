import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarter.Named.Tail.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarter.Duhamel.Head.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Duhamel.Mass

/-!
# Sixth Fréchet endpoint: quantitative nineteen-quarter Duhamel midpoint head

The selected terminal tail now has a quantitative `19/4` raw Fourier moment.
The midpoint head is the shorter-time selected Duhamel state evolved through
the strictly positive heat lag `t/2`.

The half-time Duhamel state already has a quantitative full-fourth raw Fourier
moment. Therefore only the residual heat weight

    19/4 - 4 = 3/4

is needed.

The compiled `3/4` heat multiplier gives

    |ξ|^(3/4) |H_τ(ξ)|
      ≤
    C_{3/4}(ν,τ).

Thus

    m_{19/4}(H_{t/2} D(t/2))
      ≤
    C_{3/4}(ν,t/2) m₄(D(t/2)).

The final statements transfer this estimate to the quotient-safe named
selected midpoint-head Fourier `L²` state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterDuhamelHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The `19/4` radial weight factors as a full-fourth source weight times the
residual `3/4` heat weight. -/
theorem h3FourierNineteenQuarterWeight_eq_fourth_mul_threeQuarter
    (ξ : H3FourierPoint3) :
    h3FourierNineteenQuarterWeight ξ
      =
    ‖ξ‖ ^ 4 *
      h3FourierThreeQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierNineteenQuarterWeight
    h3FourierThreeQuarterWeight

  calc
    ‖ξ‖ ^ ((19 : ℝ) / 4)
        =
      ‖ξ‖ ^ ((4 : ℝ) + ((3 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ (4 : ℝ) *
        ‖ξ‖ ^ ((3 : ℝ) / 4) := by
        rw [
          Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (4 : ℝ))
            (by norm_num : 0 ≤ (3 : ℝ) / 4)
        ]
    _ =
      ‖ξ‖ ^ 4 *
        ‖ξ‖ ^ ((3 : ℝ) / 4) := by
        have h4pow :
            ‖ξ‖ ^ (4 : ℝ) = ‖ξ‖ ^ (4 : ℕ) :=
          Real.rpow_natCast ‖ξ‖ 4
        rw [h4pow]

/-- Positive heat lag upgrades an `L²` amplitude with an integrable
full-fourth raw Fourier moment to an integrable `19/4` moment. -/
theorem h3HeatFourierSymbol_nineteenQuarter_norm_integrable_of_fourth
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hWeightContinuous :
      Continuous h3FourierNineteenQuarterWeight := by
    unfold h3FourierNineteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (19 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable F)).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 4 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF4.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_threeQuarter_le
      hν hτ ξ

  have hFourth0 :
      0 ≤ ‖ξ‖ ^ 4 :=
    pow_nonneg (norm_nonneg ξ) 4

  have hTargetNonneg :
      0 ≤
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ := by
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        C * (‖ξ‖ ^ 4 * ‖F ξ‖) :=
    mul_nonneg hC0
      (mul_nonneg hFourth0 (norm_nonneg _))

  have hBound :
      h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
        ≤
      C * (‖ξ‖ ^ 4 * ‖F ξ‖) := by
    rw [
      h3FourierNineteenQuarterWeight_eq_fourth_mul_threeQuarter,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 4 * h3FourierThreeQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 4 *
          (h3FourierThreeQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 4 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 4 *
                (h3FourierThreeQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 4 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hFourth0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 4 * ‖F ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Quantitative `19/4` positive-lag heat smoothing from a full-fourth raw
Fourier mass. -/
theorem h3HeatFourierSymbol_nineteenQuarter_norm_integral_le_of_fourth
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatThreeQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν τ

  have hTarget :=
    h3HeatFourierSymbol_nineteenQuarter_norm_integrable_of_fourth
      hν hτ F hF4

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 4 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF4.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C * (‖ξ‖ ^ 4 * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_threeQuarter_le
        hν hτ ξ

    have hFourth0 :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg (norm_nonneg ξ) 4

    rw [
      h3FourierNineteenQuarterWeight_eq_fourth_mul_threeQuarter,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 4 * h3FourierThreeQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 4 *
          (h3FourierThreeQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 4 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 4 *
                (h3FourierThreeQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 4 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hFourth0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 4 * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  dsimp only [C] at hIntegral ⊢

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatThreeQuarterMomentCoefficient ν τ *
          (‖ξ‖ ^ 4 * ‖F ξ‖) :=
      hIntegral
    _ =
      h3HeatThreeQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖F ξ‖) := by
      rw [integral_const_mul]

/-- Explicit `19/4` raw Fourier mass envelope for one selected midpoint-head
coordinate. -/
noncomputable def h3SelectedDuhamelHeadNineteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
    h3SelectedDuhamelFourthMomentEnvelope ν A (t / 2)

/-- The named selected positive-lag Duhamel head has an integrable `19/4` raw
Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineteenQuarterMoment_integrable
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
        h3FourierNineteenQuarterWeight ξ *
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

  have hD4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeat :=
    h3HeatFourierSymbol_nineteenQuarter_norm_integrable_of_fourth
      hν hhalf0 D hD4

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  refine hHeat.congr ?_
  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Quantitative `19/4` raw Fourier mass bound for the named selected midpoint
head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineteenQuarterMomentMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadNineteenQuarterMomentEnvelope ν A t := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalfR :
      t / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) htR

  have hD4 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeatBound :=
    h3HeatFourierSymbol_nineteenQuarter_norm_integral_le_of_fourth
      hν hhalf0 D hD4

  have hD4Bound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelFourthMomentEnvelope ν A (t / 2) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integral_le
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hCoeff0 :
      0 ≤ h3HeatThreeQuarterMomentCoefficient ν (t / 2) :=
    h3HeatThreeQuarterMomentCoefficient_nonneg
      hν.le hhalf0.le

  unfold h3SelectedDuhamelHeadNineteenQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ :=
      hIntegralEq
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖) :=
      hHeatBound
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
        h3SelectedDuhamelFourthMomentEnvelope ν A (t / 2) :=
      mul_le_mul_of_nonneg_left hD4Bound hCoeff0

end
end Euclidean
end Bridge
end PrimeTensor
