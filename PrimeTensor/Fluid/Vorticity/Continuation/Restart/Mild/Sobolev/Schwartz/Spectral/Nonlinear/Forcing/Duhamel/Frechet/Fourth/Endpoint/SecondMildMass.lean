import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SecondDuhamelMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildRawSecond

/-!
# Quantitative second Fourier moment of the selected positive-time mild state

The selected mild coordinate has the exact raw Fourier decomposition

    W(t)_i = H_t U₀_i + D(t)_i.

Both pieces now carry explicit second-moment estimates:

* `SecondHeatMass` bounds the positive-time free heat contribution;
* `SecondDuhamelMass` bounds the complete selected Duhamel contribution.

This file adds the two budgets at the quotient-safe raw Fourier `L²` level and
then uses the already-compiled `MildRawSecond` representation bridge to transfer
the exact same numerical estimate to the canonical pointwise raw Fourier
representative consumed by the nonlinear forcing layer.

Thus this checkpoint gives the first explicit positive-time `m₂` bound for the
actual selected mild state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointSecondMildMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw Fourier second mass of a scalar spectral H³ state. -/
noncomputable def h3SpectralScalarRawFourierSecondMass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- Pointwise positive-time second-moment envelope for one selected mild
coordinate. -/
noncomputable def h3SelectedMildSecondMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatSecondMomentRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A
    +
  h3SelectedDuhamelSecondMomentEnvelope ν A t

/-- The named quotient-safe raw Fourier `L²` state of one selected mild
coordinate has second moment bounded by the sum of the explicit free-heat and
full-Duhamel budgets. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_secondMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildSecondMomentEnvelope ν A t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeatInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_secondMoment_integrable
        hν U₀ ht i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖ +
            ‖ξ‖ ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖
          ≤
        ‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖D ξ‖ := by
    intro ξ

    have hw : 0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg (norm_nonneg ξ) 2

    calc
      ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖
          ≤
        ‖ξ‖ ^ 2 * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (H ξ) (D ξ))
          hw
      _ =
        ‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_secondMoment_integral_le
        hν U₀ hA hU₀ ht i

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelSecondMomentEnvelope ν A t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integral_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildSecondMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ - D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatSecondMomentRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient *
          A
        +
      h3SelectedDuhamelSecondMomentEnvelope ν A t :=
      add_le_add hHeatBound hDuhamelBound

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has the same quantitative second-moment bound. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierSecondMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ t i)
      ≤
    h3SelectedMildSecondMomentEnvelope ν A t := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_secondMoment_integral_le
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_secondMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierSecondMass
  rw [hIntegralEq]
  exact hNamed

/-- Raw Fourier second mass is nonnegative. -/
theorem h3SpectralScalarRawFourierSecondMass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierSecondMass F := by
  unfold h3SpectralScalarRawFourierSecondMass
  exact integral_nonneg fun ξ => by
    exact
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) 2)
        (norm_nonneg _)

end
end Euclidean
end Bridge
end PrimeTensor
