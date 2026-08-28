import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdDuhamelMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildRawSecond

/-!
# Quantitative third Fourier moment of the selected positive-time mild state

The selected mild coordinate has the exact raw Fourier decomposition

    W(t)_i = H_t U₀_i + D(t)_i.

Both pieces now carry quantitative third-moment estimates:

* `ThirdHeatMass` bounds the positive-time free heat contribution;
* `ThirdDuhamelMass` bounds the complete selected Duhamel contribution.

This file adds the two budgets at the quotient-safe raw Fourier `L²` level and
then transfers the same numerical estimate to the canonical pointwise raw
Fourier representative consumed by the nonlinear forcing layer.

Thus the selected positive-time mild state now has a fully quantitative third
raw Fourier moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFourthEndpointThirdMildMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Raw Fourier third mass of a scalar spectral H³ state. -/
noncomputable def h3SpectralScalarRawFourierThirdMass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 3 *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- Pointwise positive-time third-moment envelope for one selected mild
coordinate. -/
noncomputable def h3SelectedMildThirdMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatThirdMomentRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A
    +
  h3SelectedDuhamelThirdMomentEnvelope ν A t

/-- The named free positive-time heat term has an integrable third raw Fourier
moment. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_thirdMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t (U₀ i) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht (U₀ i) 3 (by norm_num)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeighted.symm

/-- Every positive-time coordinate of the named selected mild raw Fourier `L²`
state has an integrable third moment throughout the restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_thirdMoment_integrable
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
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_thirdMoment_integrable
        hν U₀ ht i

  have hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ‖ +
            ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat.add hDuhamel

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 3).aestronglyMeasurable).mul
        (MeasureTheory.Lp.aestronglyMeasurable W).norm

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards [hRep] with ξ hξ

  have hw : 0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 3 * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖
        ≤
      ‖ξ‖ ^ 3 * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (D ξ))
        hw
    _ =
      ‖ξ‖ ^ 3 * ‖H ξ‖ +
        ‖ξ‖ ^ 3 * ‖D ξ‖ := by
      ring

/-- The named quotient-safe raw Fourier `L²` state of one selected mild
coordinate has third moment bounded by the sum of the explicit free-heat and
full-Duhamel budgets. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_thirdMoment_integral_le
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
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildThirdMomentEnvelope ν A t := by
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
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_thirdMoment_integrable
        hν U₀ ht i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖H ξ‖ +
            ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖
          ≤
        ‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖D ξ‖ := by
    intro ξ

    have hw : 0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3

    calc
      ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖
          ≤
        ‖ξ‖ ^ 3 * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (D ξ))
          hw
      _ =
        ‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ‖)
        ≤
      h3HeatThirdMomentRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_thirdMoment_integral_le
        hν U₀ hA hU₀ ht i

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentEnvelope ν A t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integral_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildThirdMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖H ξ + D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (‖ξ‖ ^ 3 * ‖H ξ‖ +
          ‖ξ‖ ^ 3 * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatThirdMomentRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient *
          A
        +
      h3SelectedDuhamelThirdMomentEnvelope ν A t :=
      add_le_add hHeatBound hDuhamelBound

/-- The weighted third-moment density of the canonical raw Fourier
representative agrees almost everywhere with the named selected mild raw
Fourier `L²` package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_thirdMoment_ae_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 3 *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 3 *
        ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ t i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := t)
      hν U₀ hA hU₀ i

  filter_upwards [hRep] with ξ hξ
  rw [← hξ]

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has an integrable third moment. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
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
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_thirdMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_thirdMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  exact hNamed.congr hEq.symm

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has the same quantitative third-moment bound. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierThirdMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ t i)
      ≤
    h3SelectedMildThirdMomentEnvelope ν A t := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_thirdMoment_integral_le
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_thirdMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierThirdMass
  rw [hIntegralEq]
  exact hNamed

/-- Raw Fourier third mass is nonnegative. -/
theorem h3SpectralScalarRawFourierThirdMass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierThirdMass F := by
  unfold h3SpectralScalarRawFourierThirdMass
  exact integral_nonneg fun ξ => by
    exact
      mul_nonneg
        (pow_nonneg (norm_nonneg ξ) 3)
        (norm_nonneg _)

end
end Euclidean
end Bridge
end PrimeTensor
