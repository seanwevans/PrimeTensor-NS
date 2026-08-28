import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SecondConvolutionMassBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFirst

/-!
# Quantitative first raw Fourier moment of the selected nonlinear forcing

`SecondConvolutionMassBound` gives the numerical scalar estimate

    m₂(F * G)
      ≤
    2 (m₂(F)m₀(G) + m₀(F)m₂(G)).

The nonlinear forcing spends one Fourier power on the divergence derivative.
Since

    ‖∂ⱼ(ξ)‖ ≤ (2π) ‖ξ‖,

the first forcing moment is bounded by `(2π)` times the second convolution
moment.  This file propagates that estimate through

1. the finite outer-product divergence sum;
2. the finite Leray projection sum.

Finally it specializes to the selected positive-time mild state.  The two
state inputs are already quantitative:

    m₀(W(t)_k) ≤ M₀(A),
    m₂(W(t)_k) ≤ M₂(ν,A,t).

Thus every selected forcing coordinate gets one explicit first-moment
envelope depending only on the already-closed zeroth and second state budgets.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFirstForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- First raw Fourier mass after one derivative hits one exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionFirstMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one divergence derivative costs at most `(2π)` times the second
raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionFirstMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFirstMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionSecondMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_firstMoment_integrable_of_secondMoment
      F G j hConv2

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv2.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

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
          (‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionFirstMass
  unfold h3RawProductConvolutionSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative scalar derivative estimate in terms of the two input
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionFirstMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionFirstMass F G j
      ≤
    (2 * Real.pi) *
      (2 *
        (h3SpectralScalarRawFourierSecondMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierSecondMass G)) := by
  have hConv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawProductConvolution_secondMoment_integrable_of
      F G hF2 hG2

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionFirstMass_le
      F G j hConv2

  have hConvMass :=
    h3RawProductConvolutionSecondMass_le
      F G hF2 hG2

  have hTwoPi0 : 0 ≤ 2 * Real.pi := by
    positivity

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left hConvMass hTwoPi0)

/-- First raw Fourier mass of one finite outer-product divergence coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceFirstMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ *
      ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- First raw Fourier mass of one Leray coefficient times one divergence
coordinate. -/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ *
      ‖h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ‖

/-- First raw Fourier mass of one complete finite Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceFirstMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- The divergence first mass is bounded by the sum of its three scalar
derivative-convolution first masses. -/
theorem h3RawFinOuterProductDivergenceFirstMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv2 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinOuterProductDivergenceFirstMass U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionFirstMass
        (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ =>
      ‖ξ‖ * ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_firstMoment_integrable_of_secondMoment
        (U i) (V j) j (hConv2 j)

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinOuterProductDivergence_firstMoment_integrable_of_convolutionSecond
      U V i hConv2

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
        ‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖
          ≤
        ∑ j : Fin 3, mterm j ξ := by
    filter_upwards with ξ

    have hSum :
        ‖∑ j : Fin 3, term j ξ‖
          ≤
        ∑ j : Fin 3, ‖term j ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

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

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3, mterm j ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceFirstMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
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
        h3FourierDerivativeRawProductConvolutionFirstMass
          (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- One bounded Leray coefficient costs at most a factor `2` in first mass. -/
theorem h3LerayCoefficientRawFinOuterProductDivergenceFirstMass_le
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
        U V i k
      ≤
    2 * h3RawFinOuterProductDivergenceFirstMass U V k := by
  have hTarget :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_firstMoment_integrable
      U V i k hDiv1

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (‖ξ‖ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv1.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 *
          (‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    filter_upwards with ξ

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
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          (norm_nonneg _)
      _ =
        2 *
          (‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
  unfold h3RawFinOuterProductDivergenceFirstMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 *
          (‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- The complete Leray-projected forcing first mass is at most twice the sum of
the three divergence-coordinate first masses. -/
theorem h3RawFinLerayOuterProductDivergenceFirstMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv1 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFirstMass U V i
      ≤
    2 * ∑ k : Fin 3,
      h3RawFinOuterProductDivergenceFirstMass U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ =>
      ‖ξ‖ * ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_firstMoment_integrable
        U V i k (hDiv1 k)

  have hTarget :=
    h3RawFinLerayOuterProductDivergence_firstMoment_integrable_of_divergenceFirst
      U V i hDiv1

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
        ‖ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        ∑ k : Fin 3, mterm k ξ := by
    filter_upwards with ξ

    have hSum :
        ‖∑ k : Fin 3, term k ξ‖
          ≤
        ∑ k : Fin 3, ‖term k ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

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

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
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
        h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
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
          h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
            U V i k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl

  have hCoeffSum :
      (∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
            U V i k)
        ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceFirstMass U V k := by
    exact
      Finset.sum_le_sum fun k _ =>
        h3LerayCoefficientRawFinOuterProductDivergenceFirstMass_le
          U V i k (hDiv1 k)

  unfold h3RawFinLerayOuterProductDivergenceFirstMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceFirstMass
          U V i k :=
      hSumIntegral
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceFirstMass U V k :=
      hCoeffSum
    _ =
      2 * ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceFirstMass U V k := by
      rw [Finset.mul_sum]

/-- Fully quantitative finite forcing estimate in terms of coordinatewise
unweighted and second state masses. -/
theorem h3RawFinLerayOuterProductDivergenceFirstMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV2 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceFirstMass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 *
              (h3SpectralScalarRawFourierSecondMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierSecondMass (V j))) := by
  have hConv2 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_secondMoment_integrable_of
        (U k) (V j) (hU2 k) (hV2 j)

  have hDiv1 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_firstMoment_integrable_of_convolutionSecond
        U V k (hConv2 k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceFirstMass_le
      U V i hDiv1

  have hDivBounds :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceFirstMass U V k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFirstMass
            (U k) (V j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceFirstMass_le
        U V k (hConv2 k)

  have hDerivativeBounds :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionFirstMass
            (U k) (V j) j
          ≤
        (2 * Real.pi) *
          (2 *
            (h3SpectralScalarRawFourierSecondMass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j) +
              h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierSecondMass (V j))) := by
    intro k j
    exact
      h3FourierDerivativeRawProductConvolutionFirstMass_le_stateMasses
        (U k) (V j) j (hU2 k) (hV2 j)

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceFirstMass U V k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFirstMass
            (U k) (V j) j := by
    exact
      Finset.sum_le_sum fun k _ => hDivBounds k

  have hDerivativeSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionFirstMass
            (U k) (V j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 *
              (h3SpectralScalarRawFourierSecondMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierSecondMass (V j))) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hDerivativeBounds k j

  have hTwo0 : 0 ≤ (2 : ℝ) := by
    norm_num

  calc
    h3RawFinLerayOuterProductDivergenceFirstMass U V i
        ≤
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceFirstMass U V k :=
      hLeray
    _ ≤
      2 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionFirstMass
              (U k) (V j) j) :=
      mul_le_mul_of_nonneg_left hDivSum hTwo0
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (2 *
                (h3SpectralScalarRawFourierSecondMass (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierSecondMass (V j))) :=
      mul_le_mul_of_nonneg_left hDerivativeSum hTwo0

/-- Explicit selected-state first forcing envelope. -/
noncomputable def h3SelectedForcingFirstMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (2 *
            (h3SelectedMildSecondMomentEnvelope ν A t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildSecondMomentEnvelope ν A t))

/-- Every selected forcing coordinate has its first raw Fourier mass bounded by
the explicit zeroth/second state envelope. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_firstMass_le
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
    h3RawFinLerayOuterProductDivergenceFirstMass
        (W t) (W t) i
      ≤
    h3SelectedForcingFirstMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
        hν U₀ hA hU₀ ht htR k

  have hBase :=
    h3RawFinLerayOuterProductDivergenceFirstMass_le_stateMasses
      (W t) (W t) i hW2 hW2

  have hW0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (W t k)
          ≤
        h3SelectedRestartRawFourierL1Envelope A := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_le
        hν U₀ hA hU₀ t k

  have hWm2 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierSecondMass (W t k)
          ≤
        h3SelectedMildSecondMomentEnvelope ν A t := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMass_le
        hν U₀ hA hU₀ ht htR k

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM2nonneg :
      0 ≤ h3SelectedMildSecondMomentEnvelope ν A t := by
    let k0 : Fin 3 := 0
    have hMass0 :
        0 ≤ h3SpectralScalarRawFourierSecondMass (W t k0) :=
      h3SpectralScalarRawFourierSecondMass_nonneg (W t k0)
    exact le_trans hMass0 (hWm2 k0)

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (2 *
              (h3SpectralScalarRawFourierSecondMass (W t k) *
                  h3SpectralScalarRawFourierL1Mass (W t j) +
                h3SpectralScalarRawFourierL1Mass (W t k) *
                  h3SpectralScalarRawFourierSecondMass (W t j)))
          ≤
        (2 * Real.pi) *
            (2 *
              (h3SelectedMildSecondMomentEnvelope ν A t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentEnvelope ν A t)) := by
    intro k j

    have hk0 :=
      h3SpectralScalarRawFourierL1Mass_nonneg (W t k)
    have hj0 :=
      h3SpectralScalarRawFourierL1Mass_nonneg (W t j)
    have hk2 :=
      h3SpectralScalarRawFourierSecondMass_nonneg (W t k)
    have hj2 :=
      h3SpectralScalarRawFourierSecondMass_nonneg (W t j)

    have hLeft :
        h3SpectralScalarRawFourierSecondMass (W t k) *
            h3SpectralScalarRawFourierL1Mass (W t j)
          ≤
        h3SelectedMildSecondMomentEnvelope ν A t *
          h3SelectedRestartRawFourierL1Envelope A :=
      mul_le_mul
        (hWm2 k)
        (hW0 j)
        hj0
        hM2nonneg

    have hRight :
        h3SpectralScalarRawFourierL1Mass (W t k) *
            h3SpectralScalarRawFourierSecondMass (W t j)
          ≤
        h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildSecondMomentEnvelope ν A t :=
      mul_le_mul
        (hW0 k)
        (hWm2 j)
        hj2
        hM0nonneg

    have hSum :=
      add_le_add hLeft hRight

    have hTwo :
        2 *
            (h3SpectralScalarRawFourierSecondMass (W t k) *
                h3SpectralScalarRawFourierL1Mass (W t j) +
              h3SpectralScalarRawFourierL1Mass (W t k) *
                h3SpectralScalarRawFourierSecondMass (W t j))
          ≤
        2 *
            (h3SelectedMildSecondMomentEnvelope ν A t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildSecondMomentEnvelope ν A t) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)

    exact
      mul_le_mul_of_nonneg_left hTwo (by positivity)

  have hSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 *
              (h3SpectralScalarRawFourierSecondMass (W t k) *
                  h3SpectralScalarRawFourierL1Mass (W t j) +
                h3SpectralScalarRawFourierL1Mass (W t k) *
                  h3SpectralScalarRawFourierSecondMass (W t j))))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (2 *
              (h3SelectedMildSecondMomentEnvelope ν A t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentEnvelope ν A t)) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hTerm k j

  unfold h3SelectedForcingFirstMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum (by norm_num))

end
end Euclidean
end Bridge
end PrimeTensor
