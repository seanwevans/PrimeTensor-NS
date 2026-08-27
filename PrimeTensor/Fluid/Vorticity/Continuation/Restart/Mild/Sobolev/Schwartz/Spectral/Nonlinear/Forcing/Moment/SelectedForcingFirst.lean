import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedConvolutionSecond

/-!
# First raw Fourier moment of the selected unheated nonlinear forcing

`SelectedConvolutionSecond` proves that every exact raw product convolution
formed from the selected positive-time mild state has an integrable second
Fourier moment.

The nonlinear forcing contains exactly one Fourier divergence derivative.
This file spends one of the two available convolution moments on that
derivative and retains one spare raw Fourier moment.

The finite Leray matrix is a bounded measurable multiplier, so the remaining
first moment survives the projection and the finite coordinate sums.

The main endpoint is therefore:

    ∫ ‖ξ‖ ‖P div (W ⊗ W)(ξ)‖ dξ < ∞

coordinatewise for every positive time in the canonical restart interval.

This is the unheated forcing moment needed by the third-derivative endpoint
bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedForcingFirst
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- If an exact raw product convolution has an integrable second Fourier
moment, then spending one Fourier derivative leaves an integrable first
moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_firstMoment_integrable_of_secondMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      continuous_norm.aestronglyMeasurable.mul
        hComplex.aestronglyMeasurable.norm

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv2.const_mul (2 * Real.pi)

  refine hMajorant.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖) := by
    positivity

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hBound :
      ‖ξ‖ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖) := by
    calc
      ‖ξ‖ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
              rw [norm_mul]
      _ ≤
        ‖ξ‖ *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Generic finite outer-product divergence first-moment propagation from
second moments of all scalar raw convolutions. -/
theorem h3RawFinOuterProductDivergence_firstMoment_integrable_of_convolutionSecond
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv2 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_firstMoment_integrable_of_secondMoment
        (U i) (V j) j (hConv2 j)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3, ‖ξ‖ * ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun j _ => hTerm j)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      continuous_norm.aestronglyMeasurable.mul
        (h3RawFinOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤ ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V i ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤ ∑ j : Fin 3, ‖ξ‖ * ‖term j ξ‖ := by
    exact Finset.sum_nonneg fun j _ => by positivity

  have hSum :
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

  have hBound :
      ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V i ξ‖
        ≤
      ∑ j : Fin 3, ‖ξ‖ * ‖term j ξ‖ := by
    unfold h3RawFinOuterProductDivergence
    change
      ‖ξ‖ * ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖ξ‖ * ‖term j ξ‖
    calc
      ‖ξ‖ * ‖∑ j : Fin 3, term j ξ‖
          ≤
        ‖ξ‖ * ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
      _ =
        ∑ j : Fin 3, ‖ξ‖ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- A bounded Leray coefficient preserves one raw Fourier moment of a raw
divergence coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_firstMoment_integrable
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      continuous_norm.aestronglyMeasurable.mul
        hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 * (‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv1.const_mul 2

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        2 * (‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    positivity

  have hBound :
      ‖ξ‖ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 * (‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    calc
      ‖ξ‖ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        ‖ξ‖ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
              rw [norm_mul]
      _ ≤
        ‖ξ‖ *
          (2 * ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          (norm_nonneg _)
      _ =
        2 * (‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Generic finite Leray projection preserves the first raw Fourier moment of
all raw divergence coordinates. -/
theorem h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_divergenceFirst
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv1 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ * ‖term k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_firstMoment_integrable
        U V i k (hDiv1 k)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3, ‖ξ‖ * ‖term k ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      integrable_finset_sum
        (Finset.univ : Finset (Fin 3))
        (fun k _ => hTerm k)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      continuous_norm.aestronglyMeasurable.mul
        (h3RawFinLerayOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤ ‖ξ‖ * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤ ∑ k : Fin 3, ‖ξ‖ * ‖term k ξ‖ := by
    exact Finset.sum_nonneg fun k _ => by positivity

  have hSum :
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

  have hBound :
      ‖ξ‖ * ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      ∑ k : Fin 3, ‖ξ‖ * ‖term k ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergence
    change
      ‖ξ‖ * ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖ξ‖ * ‖term k ξ‖
    calc
      ‖ξ‖ * ‖∑ k : Fin 3, term k ξ‖
          ≤
        ‖ξ‖ * ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum (norm_nonneg _)
      _ =
        ∑ k : Fin 3, ‖ξ‖ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Selected positive-time outer-product divergence retains one raw Fourier
moment after spending one of the two convolution moments on divergence. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
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
        ‖ξ‖ *
          ‖h3RawFinOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply
    h3RawFinOuterProductDivergence_firstMoment_integrable_of_convolutionSecond

  intro j
  exact
    h3RawProductConvolution_selectedRestart_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i j

/-- Main endpoint: the complete unheated selected finite Leray-divergence
forcing has one spare integrable raw Fourier moment at every positive time in
the canonical restart interval. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
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
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply
    h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_divergenceFirst

  intro k
  exact
    h3RawFinOuterProductDivergence_selectedRestart_firstMoment_integrable
      hν U₀ hA hU₀ ht htR k

end
end Euclidean
end Bridge
end PrimeTensor
