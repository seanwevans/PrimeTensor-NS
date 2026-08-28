import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarterDerivative

/-!
# Five-quarter raw Fourier moment of the selected unheated nonlinear forcing

`SelectedConvolutionNineQuarter` gives an integrable `9/4` Fourier moment for
every exact raw product convolution formed from the selected positive-time mild
state.

`FiveQuarterDerivative` spends the single Fourier derivative present in the
nonlinear divergence and leaves an integrable `5/4` moment for each scalar
derivative-convolution term.

This file lifts that scalar statement through the two finite structures in the
forcing:

1. the finite outer-product divergence sum;
2. the finite Leray projection sum.

The Leray coefficients remain bounded by `2`, so no additional frequency power
is lost.

The main endpoint is therefore

    ∫ ‖ξ‖^(5/4) ‖P div (W ⊗ W)(ξ)‖ dξ < ∞

coordinatewise for every positive time in the canonical restart interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedForcingFiveQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic finite outer-product divergence propagation: if every scalar raw
product convolution has a `9/4` moment, then the divergence coordinate has a
`5/4` moment after spending one Fourier derivative. -/
theorem h3RawFinOuterProductDivergence_fiveQuarterMoment_integrable_of_convolutionNineQuarter
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv9 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFiveQuarterWeight ξ * ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_fiveQuarterMoment_integrable_of_nineQuarterMoment
        (U i) (V j) j (hConv9 j)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3,
            h3FourierFiveQuarterWeight ξ * ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hTerm j)

  have hWeightContinuous :
      Continuous h3FourierFiveQuarterWeight := by
    unfold h3FourierFiveQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (5 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawFinOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hFive0 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ j : Fin 3,
          h3FourierFiveQuarterWeight ξ * ‖term j ξ‖ := by
    exact
      Finset.sum_nonneg fun j _ =>
        mul_nonneg hFive0 (norm_nonneg _)

  have hSum :
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

  have hBound :
      h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierFiveQuarterWeight ξ * ‖term j ξ‖ := by
    unfold h3RawFinOuterProductDivergence
    change
      h3FourierFiveQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierFiveQuarterWeight ξ * ‖term j ξ‖
    calc
      h3FourierFiveQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
          ≤
        h3FourierFiveQuarterWeight ξ *
          ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hFive0
      _ =
        ∑ j : Fin 3,
          h3FourierFiveQuarterWeight ξ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- A bounded Leray coefficient preserves the `5/4` raw Fourier moment of one
raw divergence coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_fiveQuarterMoment_integrable
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k

  have hWeightContinuous :
      Continuous h3FourierFiveQuarterWeight := by
    unfold h3FourierFiveQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (5 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierFiveQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv5.const_mul 2

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierFiveQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖ :=
    mul_nonneg hFive0 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        2 *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    exact
      mul_nonneg
        (by norm_num)
        (mul_nonneg hFive0 (norm_nonneg _))

  have hBound :
      h3FourierFiveQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 *
        (h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    calc
      h3FourierFiveQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        h3FourierFiveQuarterWeight ξ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
              rw [norm_mul]
      _ ≤
        h3FourierFiveQuarterWeight ξ *
          (2 * ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          hFive0
      _ =
        2 *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Generic finite Leray projection preserves the `5/4` raw Fourier moment of
all raw divergence coordinates. -/
theorem h3RawFinLerayOuterProductDivergence_fiveQuarterMoment_integrable_of_divergenceFiveQuarter
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv5 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFiveQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFiveQuarterWeight ξ * ‖term k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_fiveQuarterMoment_integrable
        U V i k (hDiv5 k)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3,
            h3FourierFiveQuarterWeight ξ * ‖term k ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => hTerm k)

  have hWeightContinuous :
      Continuous h3FourierFiveQuarterWeight := by
    unfold h3FourierFiveQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (5 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawFinLerayOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hFive0 (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ k : Fin 3,
          h3FourierFiveQuarterWeight ξ * ‖term k ξ‖ := by
    exact
      Finset.sum_nonneg fun k _ =>
        mul_nonneg hFive0 (norm_nonneg _)

  have hSum :
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

  have hBound :
      h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierFiveQuarterWeight ξ * ‖term k ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergence
    change
      h3FourierFiveQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierFiveQuarterWeight ξ * ‖term k ξ‖
    calc
      h3FourierFiveQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
          ≤
        h3FourierFiveQuarterWeight ξ *
          ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hFive0
      _ =
        ∑ k : Fin 3,
          h3FourierFiveQuarterWeight ξ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Selected positive-time outer-product divergence retains an integrable `5/4`
raw Fourier moment after the single divergence derivative is spent. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply
    h3RawFinOuterProductDivergence_fiveQuarterMoment_integrable_of_convolutionNineQuarter

  intro j
  exact
    h3RawProductConvolution_selectedRestart_nineQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i j

/-- Main endpoint: the complete unheated selected finite Leray-divergence
forcing has an integrable `5/4` raw Fourier moment at every positive time in
the canonical restart interval. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply
    h3RawFinLerayOuterProductDivergence_fiveQuarterMoment_integrable_of_divergenceFiveQuarter

  intro k
  exact
    h3RawFinOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR k

end
end Euclidean
end Bridge
end PrimeTensor
