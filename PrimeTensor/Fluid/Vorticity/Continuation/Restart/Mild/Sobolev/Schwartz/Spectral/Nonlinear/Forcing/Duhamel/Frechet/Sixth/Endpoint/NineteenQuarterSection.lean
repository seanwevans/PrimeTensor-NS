import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Third.Forcing.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterSection

/-!
# Sixth Fréchet endpoint: subcritical nineteen-quarter source sections

A direct full-fifth varying-source estimate is critical: pairing the selected
forcing cubic moment with two heat powers would again produce the
nonintegrable terminal kernel `(t-s)⁻¹`.

The correct first sixth-layer bootstrap is therefore slightly subcritical. At
weight `19/4`,

    19/4 = 3 + 7/4.

The selected forcing supplies the first three powers, while the residual `7/4`
heat multiplier is the already-normalized integrable majorant

    C₇(ν) (t-s)^(-7/8).

This is the exact one-moment shift of the fifth-layer `15/4` source-section
argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterSection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The radial `19/4` Fourier weight. -/
noncomputable def h3FourierNineteenQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((19 : ℝ) / 4)

/-- The `19/4` weight factors into the selected forcing cubic moment and the
residual `7/4` heat weight. -/
theorem h3FourierNineteenQuarterWeight_eq_cube_mul_sevenQuarter
    (ξ : H3FourierPoint3) :
    h3FourierNineteenQuarterWeight ξ
      =
    ‖ξ‖ ^ 3 * h3FourierSevenQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold h3FourierNineteenQuarterWeight
  unfold h3FourierSevenQuarterWeight

  calc
    ‖ξ‖ ^ ((19 : ℝ) / 4)
        =
      ‖ξ‖ ^ ((3 : ℝ) + ((7 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ (3 : ℝ) * ‖ξ‖ ^ ((7 : ℝ) / 4) := by
        rw [
          Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (3 : ℝ))
            (by norm_num : 0 ≤ (7 : ℝ) / 4)
        ]
    _ =
      ‖ξ‖ ^ 3 * ‖ξ‖ ^ ((7 : ℝ) / 4) := by
        exact
          congrArg
            (fun z : ℝ => z * ‖ξ‖ ^ ((7 : ℝ) / 4))
            (Real.rpow_natCast ‖ξ‖ 3)

/-- A positive heat lag sends an amplitude with an integrable cubic raw
Fourier moment to an amplitude with an integrable `19/4` moment. -/
theorem h3HeatFourierSymbol_nineteenQuarter_weighted_mul_integrable_of_third
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ((h3FourierNineteenQuarterWeight ξ : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatSevenQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hWeightContinuous :
      Continuous h3FourierNineteenQuarterWeight := by
    unfold h3FourierNineteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (19 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((h3FourierNineteenQuarterWeight ξ : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp hWeightContinuous).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_sevenQuarter_le
      hν hτ ξ

  have hCube0 :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hWeight0 :
      0 ≤ h3FourierNineteenQuarterWeight ξ := by
    unfold h3FourierNineteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0,
    norm_mul,
    h3FourierNineteenQuarterWeight_eq_cube_mul_sevenQuarter
  ]

  calc
    (‖ξ‖ ^ 3 * h3FourierSevenQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      ‖ξ‖ ^ 3 *
        (h3FourierSevenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
      have hScaled :
          ‖ξ‖ ^ 3 *
              (h3FourierSevenQuarterWeight ξ *
                ‖h3HeatFourierSymbol ν τ ξ‖)
            ≤
          ‖ξ‖ ^ 3 * C :=
        mul_le_mul_of_nonneg_left hHeat hCube0
      exact
        mul_le_mul_of_nonneg_right
          hScaled
          (norm_nonneg (F ξ))
    _ =
      C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
      ring

/-- Quantitative one-section estimate at the `19/4` endpoint. -/
theorem h3HeatFourierSymbol_nineteenQuarter_frequencyIntegral_le
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖F ξ‖) := by
  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  let C : ℝ :=
    h3HeatSevenQuarterMomentCoefficient ν (t - s)

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hComplex :=
      h3HeatFourierSymbol_nineteenQuarter_weighted_mul_integrable_of_third
        hν hτ F hF hF3
    have hWeight0 :
        ∀ ξ : H3FourierPoint3,
          0 ≤ h3FourierNineteenQuarterWeight ξ := by
      intro ξ
      unfold h3FourierNineteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _
    simpa only [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (hWeight0 _)
    ] using hComplex.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖
          ≤
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_sevenQuarter_le
        hν hτ ξ

    have hCube0 :
        0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3

    rw [
      norm_mul,
      h3FourierNineteenQuarterWeight_eq_cube_mul_sevenQuarter
    ]

    calc
      (‖ξ‖ ^ 3 * h3FourierSevenQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν (t - s) ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 3 *
          (h3FourierSevenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 3 *
                (h3FourierSevenQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν (t - s) ξ‖)
              ≤
            ‖ξ‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left hHeat hCube0
        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  have hCeq :
      C = h3HeatSevenQuarterTerminalMajorant ν t s := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_sub_eq_terminalMajorant
        hν hs

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) :=
      hIntegral
    _ =
      C *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖F ξ‖ := by
      rw [integral_const_mul]
    _ =
      h3HeatSevenQuarterTerminalMajorant ν t s *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖F ξ‖) := by
      rw [hCeq]

/-- Selected positive-time nonlinear forcing section estimate at the
subcritical `19/4` state endpoint. -/
theorem h3SelectedForcingHeat_nineteenQuarter_frequencyIntegral_le
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let N : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergence
        (W s) (W s) i
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceThirdMass
        (W s) (W s) i := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hN3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hBase :=
    h3HeatFourierSymbol_nineteenQuarter_frequencyIntegral_le
      hν hs.2 N hN hN3

  simpa only [
    h3RawFinLerayOuterProductDivergenceThirdMass,
    N, W
  ] using hBase

end
end Euclidean
end Bridge
end PrimeTensor
