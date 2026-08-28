import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SecondDuhamelHeadMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond

/-!
# Quantitative second Fourier moment of the full selected Duhamel state

The complete selected Duhamel contribution splits at the midpoint into

    D(t) = Head(t) + Tail(t).

The two quantitative pieces are now already available:

* `SecondDuhamelHeadMass` bounds the positive-lag head by
  `h3SelectedDuhamelHeadSecondMomentEnvelope`;
* `NamedSecond`, imported through `FullSecond`, bounds the terminal tail by
  `h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget`.

This file only performs the final triangle-inequality bookkeeping at the
quotient-safe raw Fourier `L²` level.  No new nonlinear or heat estimate is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointSecondDuhamelMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit second-moment envelope for one coordinate of the complete
selected Duhamel contribution. -/
noncomputable def h3SelectedDuhamelSecondMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadSecondMomentEnvelope ν A t +
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t

/-- The complete selected Duhamel contribution has second raw Fourier mass
bounded by the sum of the quantitative midpoint-head and terminal-tail
budgets. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integral_le
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
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelSecondMomentEnvelope ν A t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ ht i

  let T : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hHeadInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hRep :
      ((D : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [D, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ ht i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖ +
            ‖ξ‖ ^ 2 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeadInt.add hTailInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖T ξ‖ := by
    intro ξ
    have hw : 0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg (norm_nonneg ξ) 2
    calc
      ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 2 * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        ‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeadBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        ≤
      h3SelectedDuhamelHeadSecondMomentEnvelope ν A t := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_secondMoment_integral_le
        hν U₀ hA hU₀ ht i

  have hTailBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖T ξ‖)
        ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
    dsimp only [T]
    exact
      integral_secondMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedDuhamelSecondMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 2 * ‖H ξ‖ +
          ‖ξ‖ ^ 2 * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖T ξ‖ := by
      rw [integral_add hHeadInt hTailInt]
    _ ≤
      h3SelectedDuhamelHeadSecondMomentEnvelope ν A t +
        h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t :=
      add_le_add hHeadBound hTailBound

end
end Euclidean
end Bridge
end PrimeTensor
