import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Duhamel.Head.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Named.Tail.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond

/-!
# Fifth Fréchet endpoint: full selected fourth Duhamel mass

The selected Duhamel contribution splits at the midpoint as

    D(t) = Head(t) + Tail(t).

Both named quotient-safe pieces now carry quantitative full-fourth raw Fourier
moments:

* `FourthDuhamelHeadMass` controls the positive-lag midpoint head;
* `FourthNamedTailMass` controls the terminal-half tail.

This file performs only the final quotient-safe triangle-inequality bookkeeping
with the radial fourth weight.  No new heat, nonlinear, or endpoint estimate is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFourthDuhamelMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit full-fourth raw Fourier moment envelope for one coordinate of the
complete selected Duhamel contribution. -/
noncomputable def h3SelectedDuhamelFourthMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadFourthMomentEnvelope ν A t +
    h3SelectedDuhamelFourthUniformBudget ν A (t / 2) t

/-- The complete selected Duhamel contribution has an integrable full-fourth
raw Fourier moment at every positive time in the restart interval. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
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
          ‖ξ‖ ^ 4 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖H ξ‖ +
            ‖ξ‖ ^ 4 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead.add hTail

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_norm.pow 4).aestronglyMeasurable.mul
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

  have hw :
      0 ≤ ‖ξ‖ ^ 4 :=
    pow_nonneg (norm_nonneg ξ) 4

  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 4 * ‖D ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖
        ≤
      ‖ξ‖ ^ 4 * (‖H ξ‖ + ‖T ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (T ξ))
        hw
    _ =
      ‖ξ‖ ^ 4 * ‖H ξ‖ +
        ‖ξ‖ ^ 4 * ‖T ξ‖ := by
      ring

/-- The complete selected Duhamel contribution has full-fourth raw Fourier mass
bounded by the sum of the quantitative midpoint-head and terminal-tail
budgets. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integral_le
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
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelFourthMomentEnvelope ν A t := by
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
          ‖ξ‖ ^ 4 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTailInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
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
        ‖ξ‖ ^ 4 * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖H ξ‖ +
            ‖ξ‖ ^ 4 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeadInt.add hTailInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 4 * ‖H ξ‖ +
          ‖ξ‖ ^ 4 * ‖T ξ‖ := by
    intro ξ

    have hw :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg (norm_nonneg ξ) 4

    calc
      ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖
          ≤
        ‖ξ‖ ^ 4 * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        ‖ξ‖ ^ 4 * ‖H ξ‖ +
          ‖ξ‖ ^ 4 * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 4 * ‖H ξ‖ +
          ‖ξ‖ ^ 4 * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeadBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖H ξ‖)
        ≤
      h3SelectedDuhamelHeadFourthMomentEnvelope ν A t := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fourthMomentMass_le
        hν U₀ hA hU₀ ht htR i

  have hTailBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖T ξ‖)
        ≤
      h3SelectedDuhamelFourthUniformBudget
        ν A (t / 2) t := by
    dsimp only [T]
    exact
      integral_fourthMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedDuhamelFourthMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 4 * ‖H ξ‖ +
          ‖ξ‖ ^ 4 * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 4 * ‖T ξ‖ := by
      rw [integral_add hHeadInt hTailInt]
    _ ≤
      h3SelectedDuhamelHeadFourthMomentEnvelope ν A t +
        h3SelectedDuhamelFourthUniformBudget
          ν A (t / 2) t :=
      add_le_add hHeadBound hTailBound

end
end Euclidean
end Bridge
end PrimeTensor
