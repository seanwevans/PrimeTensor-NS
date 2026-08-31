import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullNineQuarter
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildSecond

/-!
# Nine-quarter Fourier moment of the selected positive-time mild state

`FullNineQuarter` proves that the complete selected nonlinear Duhamel
contribution has an integrable `9/4` raw Fourier moment at every positive time
in the canonical restart interval.

The remaining term in the mild fixed-point equation is the free positive-time
heat evolution of the initial state.  The already-closed `9/4` heat multiplier
estimate gives the same moment for that term directly.

This file combines those two facts at the quotient-safe `L²` level.  For every

    0 < t ≤ h3FinHeatLerayRestartRadius ν A,

the exact selected mild equation

    W(t) = H_t U₀ - D(t)

is pushed through coordinate projection and exact H³ deweighting.  The
pointwise triangle inequality then transfers the `9/4` Fourier moment from the
heat and Duhamel pieces to the actual selected state `W(t)`.

The next checkpoint can transfer this named `L²` statement to the canonical
pointwise raw Fourier representative consumed by `h3RawProductConvolution`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedMildNineQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The named free positive-time heat term has an integrable `9/4` raw Fourier
moment. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier (U₀ i))
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 (U₀ i))

  have hWeightedComplex :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (h3FourierNineQuarterWeight ξ : ℂ) *
            (h3HeatFourierSymbol ν t ξ *
              h3SpectralScalarRawFourier (U₀ i) ξ))
        (volume : Measure H3FourierPoint3) :=
    h3HeatFourierSymbol_nineQuarter_weighted_mul_integrable
      hν ht
      (h3SpectralScalarRawFourier (U₀ i))
      hRaw

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t (U₀ i) ξ‖)
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
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeightedRep.symm

/-- Every positive-time coordinate of the actual selected mild state has an
integrable `9/4` raw Fourier moment throughout the canonical restart window. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineQuarterMoment_integrable
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
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat.add hDuhamel

  have hWeightContinuous :
      Continuous h3FourierNineQuarterWeight := by
    unfold h3FourierNineQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable W).norm

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards [hRep] with ξ hξ

  have hw :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    positivity

  have hTargetNonneg :
      0 ≤ h3FourierNineQuarterWeight ξ * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    h3FourierNineQuarterWeight ξ * ‖H ξ - D ξ‖
        ≤
      h3FourierNineQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (H ξ) (D ξ))
        hw
    _ =
      h3FourierNineQuarterWeight ξ * ‖H ξ‖ +
        h3FourierNineQuarterWeight ξ * ‖D ξ‖ := by
      ring

end
end Euclidean
end Bridge
end PrimeTensor
