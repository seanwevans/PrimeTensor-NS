import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.HeadSecond

/-!
# Second Fourier moment of the full selected Duhamel state

The midpoint decomposition of the selected Duhamel state is now controlled on
both sides:

* the positive-lag head has an integrable second raw Fourier moment;
* the terminal-half tail has an integrable second raw Fourier moment.

This file puts those two pieces back together at the quotient-safe `L²` level.

Exact H³ deweighting is linear, so the deweighted full selected Duhamel state
is exactly the sum of the deweighted named head and tail states.  The `L²`
coercion respects addition almost everywhere, and the triangle inequality then
transfers the two moment bounds to the complete selected Duhamel contribution.

This is the positive-time second-moment bootstrap input needed before feeding
the selected state back through the quadratic forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelFullSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Quotient-safe raw Fourier `L²` state of one coordinate of the complete
selected Duhamel contribution. -/
noncomputable def h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    H3FourierComplexL2 :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  h3SpectralFinCoordinateRawFourierL2CLM i
    (h3SpectralFinHeatLerayDuhamel
      ν t hν W W)

/-- Exact midpoint decomposition after coordinate projection and H³
deweighting. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_eq_head_add_tail
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i
      =
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i
      +
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := t) hν U₀ hA hU₀ i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hSplit :
      h3SpectralFinHeatLerayDuhamel ν t hν W W
        =
      h3SpectralFinHeatLerayDuhamelHead ν t hν ht W W
        +
      h3SpectralFinHeatLerayDuhamelSelectedTail
        (t := t) hν U₀ hA hU₀ := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayDuhamel_selectedRestart_eq_head_add_tail
        hν U₀ hA hU₀ ht

  have hMap :=
    congrArg
      (h3SpectralFinCoordinateRawFourierL2CLM i)
      hSplit

  dsimp only [
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2,
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2,
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2,
    W
  ]

  simpa only [
    map_add,
    h3SpectralFinCoordinateRawFourierL2CLM_apply
  ] using hMap

/-- The coercion of the complete selected Duhamel raw Fourier `L²` state agrees
almost everywhere with the pointwise sum of the named head and tail
representatives. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    ((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ
        +
      ((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
          (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ) ξ) := by
  rw [
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_eq_head_add_tail
      hν U₀ hA hU₀ ht i
  ]

  exact
    MeasureTheory.Lp.coeFn_add
      (h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i)
      (h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
        (t := t) hν U₀ hA hU₀ i)

/-- The complete selected Duhamel contribution has an integrable second raw
Fourier moment at every positive time in the restart interval. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_secondMoment_integrable
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
        ‖ξ‖ ^ 2 *
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

  let F : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hHead :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖H ξ‖ +
            ‖ξ‖ ^ 2 * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead.add hTail

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable F).norm

  have hRep :
      ((F : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [F, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ ht i

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hRep] with ξ hξ

  have hw : 0 ≤ ‖ξ‖ ^ 2 := pow_nonneg (norm_nonneg ξ) 2
  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 2 * ‖F ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

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

end
end Euclidean
end Bridge
end PrimeTensor
