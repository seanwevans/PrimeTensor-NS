import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterAmplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond

/-!
# Nine-quarter Fourier moment of the full selected Duhamel state

The terminal-half endpoint analysis has now produced an actual `9/4` Fourier
moment for the explicit selected tail amplitude.

This file closes the corresponding statement for the complete named selected
Duhamel contribution.

There are three steps.

1. Transfer the terminal-tail `9/4` moment from the explicit raw amplitude to
   the quotient-safe named tail `L²` state using the already-established a.e.
   representative identity.
2. Treat the midpoint head.  The head is the shorter-time Duhamel state evolved
   by the strictly positive heat lag `t/2`; the existing `9/4` heat smoothing
   lemma therefore gives its weighted Fourier `L¹` bound directly.
3. Use the already-proved midpoint identity

       full = head + tail

   at the deweighted `L²` level and the triangle inequality to obtain the full
   selected Duhamel `9/4` moment.

No new endpoint estimate is introduced.  This checkpoint turns the terminal
`9/4` bootstrap into a property of the actual full selected Duhamel state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedDuhamelFullNineQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted `9/4` density of the named selected terminal tail agrees
almost everywhere with the explicit raw tail amplitude density. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineQuarterWeight ξ *
        ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineQuarterWeight ξ *
        ‖h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- The actual named selected terminal-tail `L²` state has an integrable
`9/4` raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_integrable
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
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hAmplitude :=
    h3SelectedDuhamelTailRawFourierAmplitude_nineQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  exact hAmplitude.congr hEq.symm

/-- The positive-lag midpoint head has an integrable `9/4` raw Fourier moment.
The only analytic input is the positive heat lag `t/2`. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineQuarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
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
    linarith

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hWeightedComplex :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (h3FourierNineQuarterWeight ξ : ℂ) *
            (h3HeatFourierSymbol ν (t / 2) ξ *
              h3SpectralScalarRawFourier G ξ))
        (volume : Measure H3FourierPoint3) :=
    h3HeatFourierSymbol_nineQuarter_weighted_mul_integrable
      hν hhalf
      (h3SpectralScalarRawFourier G)
      hRaw

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν (t / 2) G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    have hNorm := hWeightedComplex.norm
    refine hNorm.congr ?_
    filter_upwards with ξ

    have hWeight0 :
        0 ≤ h3FourierNineQuarterWeight ξ := by
      unfold h3FourierNineQuarterWeight
      positivity

    unfold h3SpectralScalarHeatRawRepresentative
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν (t / 2) G ξ‖) := by
    dsimp only [G, W] at hRep ⊢
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeightedRep.symm

/-- The complete selected Duhamel contribution has an integrable `9/4` raw
Fourier moment at every positive time in the restart interval. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMoment_integrable
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
        h3FourierNineQuarterWeight ξ *
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
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht i

  have hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineQuarterWeight ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead.add hTail

  have hWeightContinuous :
      Continuous h3FourierNineQuarterWeight := by
    unfold h3FourierNineQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
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

  have hw :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    positivity

  have hTargetNonneg :
      0 ≤ h3FourierNineQuarterWeight ξ * ‖F ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

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

end
end Euclidean
end Bridge
end PrimeTensor
