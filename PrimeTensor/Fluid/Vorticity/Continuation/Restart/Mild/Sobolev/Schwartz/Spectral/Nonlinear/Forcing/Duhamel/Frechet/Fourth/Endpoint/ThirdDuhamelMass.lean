import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdDuhamelHeadMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdNamedTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond

/-!
# Quantitative third Fourier moment of the full selected Duhamel state

The complete selected Duhamel contribution splits at the midpoint as

    D(t) = Head(t) + Tail(t).

Both pieces now carry quantitative third raw Fourier moments:

* `ThirdDuhamelHeadMass` controls the positive-lag midpoint head;
* `ThirdNamedTailMass` controls the actual named terminal-half tail.

This file performs only the final quotient-safe triangle-inequality
bookkeeping with the cubic radial weight.  No new heat or nonlinear endpoint
estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointThirdDuhamelMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit third-moment envelope for one coordinate of the complete selected
Duhamel contribution. -/
noncomputable def h3SelectedDuhamelThirdMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadThirdMomentEnvelope ν A t +
    h3SelectedDuhamelTailThirdFullBudget ν A t

/-- The complete selected Duhamel contribution has an integrable third raw
Fourier moment at every positive time in the restart interval. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
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
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ ht i

  let T : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hHead :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ‖ +
            ‖ξ‖ ^ 3 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead.add hTail

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 3).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable D).norm

  have hRep :
      ((D : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [D, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ ht i

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards [hRep] with ξ hξ

  have hw : 0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 3 * ‖D ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖
        ≤
      ‖ξ‖ ^ 3 * (‖H ξ‖ + ‖T ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (T ξ))
        hw
    _ =
      ‖ξ‖ ^ 3 * ‖H ξ‖ +
        ‖ξ‖ ^ 3 * ‖T ξ‖ := by
      ring

/-- The complete selected Duhamel contribution has third raw Fourier mass
bounded by the sum of the quantitative midpoint-head and terminal-tail
budgets. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelThirdMomentEnvelope ν A t := by
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
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
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
        ‖ξ‖ ^ 3 * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ‖ +
            ‖ξ‖ ^ 3 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeadInt.add hTailInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖T ξ‖ := by
    intro ξ
    have hw : 0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3
    calc
      ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 3 * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        ‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeadBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        ≤
      h3SelectedDuhamelHeadThirdMomentEnvelope ν A t := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_thirdMomentMass_le
        hν U₀ hA hU₀ ht i

  have hTailBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖T ξ‖)
        ≤
      h3SelectedDuhamelTailThirdFullBudget ν A t := by
    dsimp only [T]
    exact
      integral_thirdMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedDuhamelThirdMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖T ξ‖ := by
      rw [integral_add hHeadInt hTailInt]
    _ ≤
      h3SelectedDuhamelHeadThirdMomentEnvelope ν A t +
        h3SelectedDuhamelTailThirdFullBudget ν A t :=
      add_le_add hHeadBound hTailBound

end
end Euclidean
end Bridge
end PrimeTensor
