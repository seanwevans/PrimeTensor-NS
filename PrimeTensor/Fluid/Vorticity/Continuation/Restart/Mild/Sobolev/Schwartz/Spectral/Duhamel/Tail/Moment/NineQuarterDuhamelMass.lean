import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterHeadMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullNineQuarter

/-!
# Quantitative nine-quarter Fourier mass of the full selected Duhamel state

The complete selected Duhamel contribution splits at the midpoint into

    D(t) = Head(t) + Tail(t).

The two quantitative `9/4` pieces are now available:

* `NineQuarterHeadMass` bounds the positive-lag midpoint head by
  `h3SelectedDuhamelHeadNineQuarterMomentEnvelope`;
* `NineQuarterTailStateMass`, imported through `NineQuarterHeadMass`, bounds the
  named terminal tail by `h3SelectedDuhamelTailNineQuarterBudget`.

`FullNineQuarter` already provides the quotient-safe a.e. identity

    full = head + tail

and qualitative `9/4` integrability for all three named states.

This file performs only the final triangle-inequality bookkeeping.  The
resulting explicit full selected Duhamel envelope is

    B_D,9/4 = B_head,9/4 + B_tail,9/4.

No new heat or nonlinear estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterDuhamelMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit `9/4` raw Fourier mass envelope for one coordinate of the complete
selected Duhamel contribution. -/
noncomputable def h3SelectedDuhamelNineQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t +
    h3SelectedDuhamelTailNineQuarterBudget ν A t

/-- The complete selected Duhamel contribution has `9/4` raw Fourier mass
bounded by the sum of the quantitative midpoint-head and terminal-tail
budgets. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelNineQuarterMomentEnvelope ν A t := by
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
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMoment_integrable
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
        h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeadInt.add hTailInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖T ξ‖ := by
    intro ξ

    have hw : 0 ≤ h3FourierNineQuarterWeight ξ := by
      unfold h3FourierNineQuarterWeight
      positivity

    calc
      h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierNineQuarterWeight ξ * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeadBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineQuarterMass_le
        hν U₀ hA hU₀ ht i

  have hTailBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖T ξ‖)
        ≤
      h3SelectedDuhamelTailNineQuarterBudget ν A t := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMass_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedDuhamelNineQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineQuarterWeight ξ * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ * ‖T ξ‖ := by
      rw [integral_add hHeadInt hTailInt]
    _ ≤
      h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A t +
        h3SelectedDuhamelTailNineQuarterBudget ν A t :=
      add_le_add hHeadBound hTailBound

end
end Euclidean
end Bridge
end PrimeTensor
