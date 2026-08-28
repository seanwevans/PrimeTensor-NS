import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarterDerivativeMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFiveQuarter

/-!
# Quantitative five-quarter mass of the finite nonlinear forcing

`FiveQuarterDerivativeMass` supplies the scalar numerical estimate after one
Fourier derivative.

This file propagates that bound through the two finite structures in the
unheated nonlinear forcing:

1. the outer-product divergence sum;
2. the Leray projection sum.

For a divergence coordinate `k`,

    m₅(div(U⊗V)_k)
      ≤
    ∑ j m₅(∂ⱼ(U_k * V_j)).

For a projected coordinate `i`, the coefficient bound
`‖P_{ik}(ξ)‖ ≤ 2` gives

    m₅(P div(U⊗V)_i)
      ≤
    2 ∑ k m₅(div(U⊗V)_k).

Combining with the scalar Young/derivative estimate yields an explicit forcing
mass bound entirely in terms of unweighted and `9/4` Fourier masses of the
state coordinates.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFiveQuarterForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `5/4` weighted mass of one raw finite outer-product divergence coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceFiveQuarterMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFiveQuarterWeight ξ *
      ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- `5/4` weighted mass of one Leray coefficient times one divergence
coordinate. -/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFiveQuarterWeight ξ *
      ‖h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ‖

/-- `5/4` weighted mass of one complete finite Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceFiveQuarterMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFiveQuarterWeight ξ *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- The divergence mass is bounded by the sum of its three scalar
derivative-convolution masses. -/
theorem h3RawFinOuterProductDivergenceFiveQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv9 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinOuterProductDivergenceFiveQuarterMass U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionFiveQuarterMass
        (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ =>
      h3FourierFiveQuarterWeight ξ * ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_fiveQuarterMoment_integrable_of_nineQuarterMoment
        (U i) (V j) j (hConv9 j)

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinOuterProductDivergence_fiveQuarterMoment_integrable_of_convolutionNineQuarter
      U V i hConv9

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3, mterm j ξ)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖
          ≤
        ∑ j : Fin 3, mterm j ξ := by
    filter_upwards with ξ

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hSum :
        ‖∑ j : Fin 3, term j ξ‖
          ≤
        ∑ j : Fin 3, ‖term j ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

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

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3, mterm j ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceFiveQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3, mterm j ξ :=
      hIntegral
    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3, mterm j ξ := by
      simpa using
        (MeasureTheory.integral_finsetSum
          (Finset.univ : Finset (Fin 3))
          (fun j _ => hTerm j))
    _ =
      ∑ j : Fin 3,
        h3FourierDerivativeRawProductConvolutionFiveQuarterMass
          (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- One bounded Leray coefficient costs at most a factor `2` in `5/4` mass. -/
theorem h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
        U V i k
      ≤
    2 * h3RawFinOuterProductDivergenceFiveQuarterMass U V k := by
  have hTarget :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_fiveQuarterMoment_integrable
      U V i k hDiv5

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierFiveQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv5.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierFiveQuarterWeight ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    filter_upwards with ξ

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

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

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
  unfold h3RawFinOuterProductDivergenceFiveQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 *
          (h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- The complete Leray-projected forcing mass is at most twice the sum of the
three divergence-coordinate masses. -/
theorem h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv5 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFiveQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass U V i
      ≤
    2 * ∑ k : Fin 3,
      h3RawFinOuterProductDivergenceFiveQuarterMass U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ =>
      h3FourierFiveQuarterWeight ξ * ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_fiveQuarterMoment_integrable
        U V i k (hDiv5 k)

  have hTarget :=
    h3RawFinLerayOuterProductDivergence_fiveQuarterMoment_integrable_of_divergenceFiveQuarter
      U V i hDiv5

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3, mterm k ξ)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        ∑ k : Fin 3, mterm k ξ := by
    filter_upwards with ξ

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hSum :
        ‖∑ k : Fin 3, term k ξ‖
          ≤
        ∑ k : Fin 3, ‖term k ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

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

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
    integral_mono_ae hTarget hMajor hDom

  have hSumIntegral :
      (∫ ξ : H3FourierPoint3,
          ∑ k : Fin 3, mterm k ξ)
        =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
          U V i k := by
    calc
      (∫ ξ : H3FourierPoint3,
          ∑ k : Fin 3, mterm k ξ)
          =
        ∑ k : Fin 3,
          ∫ ξ : H3FourierPoint3, mterm k ξ := by
        simpa using
          (MeasureTheory.integral_finsetSum
            (Finset.univ : Finset (Fin 3))
            (fun k _ => hTerm k))
      _ =
        ∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
            U V i k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl

  have hCoeffSum :
      (∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
            U V i k)
        ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceFiveQuarterMass U V k := by
    exact
      Finset.sum_le_sum fun k _ =>
        h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass_le
          U V i k (hDiv5 k)

  unfold h3RawFinLerayOuterProductDivergenceFiveQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceFiveQuarterMass
          U V i k :=
      hSumIntegral
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceFiveQuarterMass U V k :=
      hCoeffSum
    _ =
      2 * ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceFiveQuarterMass U V k := by
      rw [Finset.mul_sum]

/-- Fully quantitative finite forcing estimate in terms of coordinatewise
unweighted and `9/4` state masses. -/
theorem h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hUq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hVq :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierNineQuarterMass (V j))) := by
  have hConv9 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_nineQuarterMoment_integrable_of
        (U k) (V j) (hUq k) (hVq j)

  have hDiv5 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierFiveQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_fiveQuarterMoment_integrable_of_convolutionNineQuarter
        U V k (hConv9 k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le
      U V i hDiv5

  have hDivBounds :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceFiveQuarterMass U V k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFiveQuarterMass
            (U k) (V j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceFiveQuarterMass_le
        U V k (hConv9 k)

  have hDerivativeBounds :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionFiveQuarterMass
            (U k) (V j) j
          ≤
        (2 * Real.pi) *
          (h3FourierNineQuarterSplitCoefficient *
            (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j) +
              h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierNineQuarterMass (V j))) := by
    intro k j
    exact
      h3FourierDerivativeRawProductConvolutionFiveQuarterMass_le_stateMasses
        (U k) (V j) j (hUq k) (hVq j)

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceFiveQuarterMass U V k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFiveQuarterMass
            (U k) (V j) j := by
    exact
      Finset.sum_le_sum fun k _ => hDivBounds k

  have hDerivativeSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFiveQuarterMass
            (U k) (V j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierNineQuarterSplitCoefficient *
              (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierNineQuarterMass (V j))) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hDerivativeBounds k j

  have hTwo0 : 0 ≤ (2 : ℝ) := by
    norm_num

  calc
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass U V i
        ≤
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceFiveQuarterMass U V k :=
      hLeray
    _ ≤
      2 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionFiveQuarterMass
              (U k) (V j) j) :=
      mul_le_mul_of_nonneg_left hDivSum hTwo0
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierNineQuarterSplitCoefficient *
                (h3SpectralScalarRawFourierNineQuarterMass (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierNineQuarterMass (V j))) :=
      mul_le_mul_of_nonneg_left hDerivativeSum hTwo0

end
end Euclidean
end Bridge
end PrimeTensor
