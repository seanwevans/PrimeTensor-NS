import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FiveQuarterMajorant
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.ElevenQuarter.Forcing.Mass

/-!
# Fifth Fréchet endpoint: subcritical full-fourth source sections

The selected nonlinear forcing now carries an integrable `11/4` raw Fourier
moment.  Therefore the full fourth Fourier weight splits as

    4 = 11/4 + 5/4.

The selected forcing supplies the first `11/4` powers, while the residual
`5/4` heat multiplier is controlled by the normalized terminal majorant

    C₅(ν) (t-s)^(-5/8).

Unlike the earlier direct fourth-moment attempt from forcing `M₂`, this
terminal kernel is integrable.  Thus the full-fourth endpoint is genuinely
subcritical and requires no source subtraction or logarithmic cancellation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFourthSection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quantitative one-frequency-section estimate at the full fourth endpoint
from a source amplitude already carrying an integrable `11/4` Fourier moment. -/
theorem h3HeatFourierSymbol_fourth_frequencyIntegral_le_of_elevenQuarter
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
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
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
  have hτ :
      0 < t - s :=
    sub_pos.mpr hs

  have hBase :=
    h3HeatFourierSymbol_fourth_norm_integral_le_of_elevenQuarter
      hν hτ F hF hF11

  have hCeq :
      h3HeatFiveQuarterMomentCoefficient ν (t - s)
        =
      h3HeatFiveQuarterTerminalMajorant ν t s :=
    h3HeatFiveQuarterMomentCoefficient_sub_eq_terminalMajorant
      hν hs

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * F ξ‖)
        ≤
      h3HeatFiveQuarterMomentCoefficient ν (t - s) *
        (∫ ξ : H3FourierPoint3,
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖) :=
      hBase
    _ =
      h3HeatFiveQuarterTerminalMajorant ν t s *
        (∫ ξ : H3FourierPoint3,
          h3FourierElevenQuarterWeight ξ * ‖F ξ‖) := by
      rw [hCeq]

/-- Selected positive-time nonlinear forcing section estimate at the full
fourth state endpoint. -/
theorem h3SelectedForcingHeat_fourth_frequencyIntegral_le
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
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceElevenQuarterMass
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

  have hN11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_elevenQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hBase :=
    h3HeatFourierSymbol_fourth_frequencyIntegral_le_of_elevenQuarter
      hν hs.2 N hN hN11

  simpa only [
    h3RawFinLerayOuterProductDivergenceElevenQuarterMass,
    N, W
  ] using hBase

/-- The selected full-fourth source section is bounded directly by the explicit
selected forcing `11/4` envelope times the integrable `5/4` heat majorant. -/
theorem h3SelectedForcingHeat_fourth_frequencyIntegral_le_envelope
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
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3SelectedForcingElevenQuarterMomentEnvelope ν A s := by
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
          ‖ξ‖ ^ 4 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
        ≤
      h3HeatFiveQuarterTerminalMajorant ν t s *
        h3RawFinLerayOuterProductDivergenceElevenQuarterMass
          (W s) (W s) i := by
    dsimp only [N, W]
    exact
      h3SelectedForcingHeat_fourth_frequencyIntegral_le
        hν U₀ hA hU₀ ha hat htR hs i

  have hMass :
      h3RawFinLerayOuterProductDivergenceElevenQuarterMass
          (W s) (W s) i
        ≤
      h3SelectedForcingElevenQuarterMomentEnvelope ν A s := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_elevenQuarterMass_le
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
