import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FiveQuarterMajorant
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.FifteenQuarter.Forcing.Mass

/-!
# Sixth Fréchet endpoint: subcritical full-fifth source sections

The selected nonlinear forcing now carries an integrable `15/4` raw Fourier
moment. Therefore the full fifth Fourier weight splits as

    5 = 15/4 + 5/4.

The selected forcing supplies the first `15/4` powers, while the residual
`5/4` heat multiplier is exactly the already-closed positive-lag estimate

    C₅(ν,τ).

On a terminal source section `τ = t - s`, this becomes the integrable
majorant

    C₅(ν) (t-s)^(-5/8).

Thus the final fifth-moment endpoint remains strictly subcritical.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointFifthSection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A full fifth Fourier weight factors as a selected forcing `15/4` weight
times the residual heat `5/4` weight. -/
theorem h3FourierNorm_fifth_eq_fifteenQuarter_mul_fiveQuarter
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ 5
      =
    h3FourierFifteenQuarterWeight ξ *
      h3FourierFiveQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierFifteenQuarterWeight
    h3FourierFiveQuarterWeight

  calc
    ‖ξ‖ ^ 5
        =
      ‖ξ‖ ^ (5 : ℝ) := by
        exact (Real.rpow_natCast ‖ξ‖ 5).symm
    _ =
      ‖ξ‖ ^
        (((15 : ℝ) / 4) + ((5 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ ((15 : ℝ) / 4) *
        ‖ξ‖ ^ ((5 : ℝ) / 4) := by
      rw [
        Real.rpow_add_of_nonneg
          hξ0
          (by norm_num : 0 ≤ (15 : ℝ) / 4)
          (by norm_num : 0 ≤ (5 : ℝ) / 4)
      ]

/-- A positive heat lag sends an amplitude with an integrable `15/4` raw
Fourier moment to a complex amplitude with an integrable full-fifth weight. -/
theorem h3HeatFourierSymbol_fifth_weighted_mul_integrable_of_fifteenQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F
        (volume : Measure H3FourierPoint3))
    (hF15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (((‖ξ‖ ^ 5 : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ)))
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν τ

  have hWeightContinuous :
      Continuous (fun ξ : H3FourierPoint3 => ‖ξ‖ ^ 5) :=
    continuous_norm.pow 5

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (((‖ξ‖ ^ 5 : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ)))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp hWeightContinuous).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF15.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_fiveQuarter_le
      hν hτ ξ

  have hFifteen0 :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hFifth0 :
      0 ≤ ‖ξ‖ ^ 5 :=
    pow_nonneg (norm_nonneg ξ) 5

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hFifth0,
    norm_mul,
    h3FourierNorm_fifth_eq_fifteenQuarter_mul_fiveQuarter
  ]

  calc
    (h3FourierFifteenQuarterWeight ξ *
        h3FourierFiveQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      h3FourierFifteenQuarterWeight ξ *
        (h3FourierFiveQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      h3FourierFifteenQuarterWeight ξ * C * ‖F ξ‖ := by
      have hScaled :
          h3FourierFifteenQuarterWeight ξ *
              (h3FourierFiveQuarterWeight ξ *
                ‖h3HeatFourierSymbol ν τ ξ‖)
            ≤
          h3FourierFifteenQuarterWeight ξ * C :=
        mul_le_mul_of_nonneg_left hHeat hFifteen0

      exact
        mul_le_mul_of_nonneg_right
          hScaled
          (norm_nonneg (F ξ))
    _ =
      C *
        (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
      ring

/-- Quantitative full-fifth heat estimate against an amplitude already
carrying an integrable `15/4` Fourier moment. -/
theorem h3HeatFourierSymbol_fifth_norm_integral_le_of_fifteenQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F
        (volume : Measure H3FourierPoint3))
    (hF15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatFiveQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν τ

  have hComplex :=
    h3HeatFourierSymbol_fifth_weighted_mul_integrable_of_fifteenQuarter
      hν hτ F hF hF15

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hFifth0 :
        ∀ ξ : H3FourierPoint3, 0 ≤ ‖ξ‖ ^ 5 := by
      intro ξ
      exact pow_nonneg (norm_nonneg ξ) 5

    simpa only [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (hFifth0 _)
    ] using hComplex.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF15.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C *
          (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_fiveQuarter_le
        hν hτ ξ

    have hFifteen0 :
        0 ≤ h3FourierFifteenQuarterWeight ξ := by
      unfold h3FourierFifteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    rw [
      norm_mul,
      h3FourierNorm_fifth_eq_fifteenQuarter_mul_fiveQuarter
    ]

    calc
      (h3FourierFifteenQuarterWeight ξ *
          h3FourierFiveQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierFifteenQuarterWeight ξ *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierFifteenQuarterWeight ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierFifteenQuarterWeight ξ *
                (h3FourierFiveQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierFifteenQuarterWeight ξ * C :=
          mul_le_mul_of_nonneg_left hHeat hFifteen0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C *
          (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C *
          (h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) :=
      hIntegral
    _ =
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
      rw [integral_const_mul]
    _ =
      h3HeatFiveQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
      rfl

/-- Quantitative one-frequency-section estimate at the full fifth endpoint
from a source amplitude already carrying an integrable `15/4` Fourier moment. -/
theorem h3HeatFourierSymbol_fifth_frequencyIntegral_le_of_fifteenQuarter
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F
        (volume : Measure H3FourierPoint3))
    (hF15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
  have hτ :
      0 < t - s :=
    sub_pos.mpr hs

  have hBase :=
    h3HeatFourierSymbol_fifth_norm_integral_le_of_fifteenQuarter
      hν hτ F hF hF15

  have hCeq :
      h3HeatFiveQuarterMomentCoefficient ν (t - s)
        =
      h3HeatFiveQuarterTerminalMajorant ν t s :=
    h3HeatFiveQuarterMomentCoefficient_sub_eq_terminalMajorant
      hν hs

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        ≤
      h3HeatFiveQuarterMomentCoefficient ν (t - s) *
        (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) :=
      hBase
    _ =
      h3HeatFiveQuarterTerminalMajorant ν t s *
        (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖F ξ‖) := by
      rw [hCeq]

/-- Selected positive-time nonlinear forcing section estimate at the full
fifth state endpoint. -/
theorem h3SelectedForcingHeat_fifth_frequencyIntegral_le
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
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
        (W s) (W s) i := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hs0 :
      0 < s :=
    lt_trans ha hs.1

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hN :
      Integrable N
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hN15 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hBase :=
    h3HeatFourierSymbol_fifth_frequencyIntegral_le_of_fifteenQuarter
      hν hs.2 N hN hN15

  simpa only [
    h3RawFinLerayOuterProductDivergenceFifteenQuarterMass,
    N, W
  ] using hBase

/-- The selected full-fifth source section is bounded directly by the explicit
selected forcing `15/4` envelope times the integrable `5/4` heat majorant. -/
theorem h3SelectedForcingHeat_fifth_frequencyIntegral_le_envelope
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
        ‖ξ‖ ^ 5 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3SelectedForcingFifteenQuarterMomentEnvelope ν A s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hs0 :
      0 < s :=
    lt_trans ha hs.1

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hSection :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 5 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
        ≤
      h3HeatFiveQuarterTerminalMajorant ν t s *
        h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
          (W s) (W s) i := by
    dsimp only [N, W]
    exact
      h3SelectedForcingHeat_fifth_frequencyIntegral_le
        hν U₀ hA hU₀ ha hat htR hs i

  have hMass :
      h3RawFinLerayOuterProductDivergenceFifteenQuarterMass
          (W s) (W s) i
        ≤
      h3SelectedForcingFifteenQuarterMomentEnvelope ν A s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fifteenQuarterMass_le
        hν U₀ hA hU₀ hs0 hsR i

  have hHeat0 :
      0 ≤ h3HeatFiveQuarterTerminalMajorant ν t s := by
    unfold h3HeatFiveQuarterTerminalMajorant
    exact
      mul_nonneg
        (Real.rpow_nonneg
          (by positivity : 0 ≤ 3 * ν⁻¹)
          _)
        (Real.rpow_nonneg
          (sub_nonneg.mpr hs.2.le)
          _)

  exact
    le_trans hSection
      (mul_le_mul_of_nonneg_left
        hMass hHeat0)

end
end Euclidean
end Bridge
end PrimeTensor
