import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Heat.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarter.Head.Mass

/-!
# Quantitative third Fourier moment of the selected Duhamel midpoint head

The selected midpoint Duhamel head is the half-time Duhamel state evolved
through the strictly positive heat lag `t/2`.

`ThirdHeatMass` gives

    ∫ |ξ|³ |H_{t/2} G|
      ≤
    C₃(ν,t/2) C_dw ‖G‖,

while `SecondDuhamelHeadMass` already provides

    ‖G‖ ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A t.

This file combines those two quantitative facts and transfers the result to
the existing quotient-safe selected midpoint-head Fourier state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdDuhamelHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit third raw Fourier mass envelope for one selected midpoint-head
coordinate. -/
noncomputable def h3SelectedDuhamelHeadThirdMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
    h3RawFourierL1DeweightingCoefficient *
    h3SelectedDuhamelHalfTimeH3Envelope ν A t

theorem h3SelectedDuhamelHeadThirdMomentEnvelope_nonneg
    {ν A t : ℝ}
    (hA : 0 ≤ A) :
    0 ≤ h3SelectedDuhamelHeadThirdMomentEnvelope ν A t := by
  unfold h3SelectedDuhamelHeadThirdMomentEnvelope
  exact
    mul_nonneg
      (mul_nonneg
        (h3HeatThirdMomentRawL1Coefficient_nonneg ν (t / 2))
        h3RawFourierL1DeweightingCoefficient_nonneg)
      (h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA)

/-- Quantitative third raw Fourier mass of the explicit heat representative
underlying the selected Duhamel midpoint head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHead_thirdMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let G : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
      ≤
    h3SelectedDuhamelHeadThirdMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hhalf : 0 < t / 2 := by
    positivity

  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_thirdMoment_integral_le_norm
      hν hhalf G

  have hG :
      ‖G‖
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    dsimp only [G, W]
    exact
      norm_h3SpectralFinHeatLerayDuhamel_selectedRestart_halfTime_coordinate_le
        hν U₀ hA hU₀ ht i

  have hCoeff0 :
      0 ≤
        h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      (h3HeatThirdMomentRawL1Coefficient_nonneg ν (t / 2))
      h3RawFourierL1DeweightingCoefficient_nonneg

  unfold h3SelectedDuhamelHeadThirdMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖)
        ≤
      h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ :=
      hHeat
    _ ≤
      h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
        h3RawFourierL1DeweightingCoefficient *
        h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
      mul_le_mul_of_nonneg_left hG hCoeff0

/-- The named quotient-safe selected midpoint-head state has an integrable
third raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_thirdMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hhalf : 0 < t / 2 := by
    positivity

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hHeatInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν (t / 2) G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν hhalf G 3 (by norm_num)

  refine hHeatInt.congr ?_
  dsimp only [G, W] at hRep ⊢
  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Quantitative third raw Fourier mass transferred to the named quotient-safe
selected Duhamel midpoint-head state. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_thirdMomentMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadThirdMomentEnvelope ν A t := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖ := by
    apply integral_congr_ae
    dsimp only [G, W] at hRep ⊢
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  dsimp only [G, W]

  exact
    h3SpectralFinHeatLerayDuhamelSelectedHead_thirdMoment_integral_le
      hν U₀ hA hU₀ ht i

end
end Euclidean
end Bridge
end PrimeTensor
