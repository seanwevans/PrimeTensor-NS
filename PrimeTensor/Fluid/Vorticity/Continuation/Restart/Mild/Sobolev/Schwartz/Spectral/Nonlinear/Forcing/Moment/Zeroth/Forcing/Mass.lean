import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.First.Convolution.Mass.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.First.Forcing.Mass

/-!
# Quantitative zeroth raw Fourier mass of the selected nonlinear forcing

The frozen `9/4` endpoint needs a quantitative quarter moment of the terminal
forcing.  Since

    |ξ|^(1/4) ≤ 1 + |ξ|,

that quarter moment is controlled by zeroth plus first forcing masses.
`FirstForcingMass` already closes the first mass.

This file closes the missing zeroth forcing mass from the quantitative first
raw convolution mass in `FirstConvolutionMassBound`.

One divergence derivative obeys

    |∂ⱼ(ξ)| ≤ (2π)|ξ|,

so

    m₀(∂ⱼ(F * G)) ≤ (2π) m₁(F * G).

The finite outer-product divergence is bounded by the sum of its derivative
terms, and the Leray projection contributes the familiar factor `2`.

The selected specialization substitutes the already-closed state envelopes

    m₀(W(t)_k) ≤ M₀(A),
    m₂(W(t)_k) ≤ M₂(ν,A,t).

Thus the selected forcing now has explicit zeroth and first raw Fourier
budgets at every positive restart time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzZerothForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Zeroth raw Fourier mass after one derivative hits one exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionL1Mass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3FourierDerivativeSymbol j ξ *
      h3RawProductConvolution F G ξ‖

/-- One divergence derivative costs at most `(2π)` times the first raw
convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionL1Mass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3) :
    h3FourierDerivativeRawProductConvolutionL1Mass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionFirstMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_integrable
      F G j

  have hFirst :=
    h3RawProductConvolution_firstMoment_integrable F G

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFirst.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    calc
      ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖
          =
        ‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawProductConvolution F G ξ‖ := by
        rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3RawProductConvolution F G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ)
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

  have hIntegral :=
    integral_mono_ae hTarget.norm hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionL1Mass
  unfold h3RawProductConvolutionFirstMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative scalar derivative estimate in terms of the two input
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionL1Mass_le_stateMasses
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
    h3FourierDerivativeRawProductConvolutionL1Mass F G j
      ≤
    (2 * Real.pi) *
      (h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierL1Mass G
        +
        2 *
          (h3SpectralScalarRawFourierSecondMass F *
              h3SpectralScalarRawFourierL1Mass G +
            h3SpectralScalarRawFourierL1Mass F *
              h3SpectralScalarRawFourierSecondMass G)) := by
  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionL1Mass_le
      F G j

  have hFirst :=
    h3RawProductConvolutionFirstMass_le_stateMasses
      F G hF2 hG2

  have hTwoPi0 : 0 ≤ 2 * Real.pi := by
    positivity

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left hFirst hTwoPi0)

/-- Zeroth raw Fourier mass of one raw finite outer-product divergence
coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceL1Mass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- Zeroth raw Fourier mass of one Leray coefficient times one divergence
coordinate. -/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3LerayCoefficient ξ i k *
      h3RawFinOuterProductDivergence U V k ξ‖

/-- The divergence zeroth mass is bounded by the sum of its three scalar
derivative-convolution zeroth masses. -/
theorem h3RawFinOuterProductDivergenceL1Mass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinOuterProductDivergenceL1Mass U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionL1Mass
        (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact
      (h3FourierDerivative_mul_rawProductConvolution_integrable
        (U i) (V j) j).norm

  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawFinOuterProductDivergence_integrable U V i).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3, mterm j ξ)
        (volume : Measure H3FourierPoint3) :=
    integrable_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
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
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖

    exact hSum

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
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
        h3FourierDerivativeRawProductConvolutionL1Mass
          (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- One bounded Leray coefficient costs at most a factor `2` in zeroth mass. -/
theorem h3LerayCoefficientRawFinOuterProductDivergenceL1Mass_le
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) :
    h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
        U V i k
      ≤
    2 * h3RawFinOuterProductDivergenceL1Mass U V k := by
  have hTarget :=
    (h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k).norm

  have hDiv :=
    (h3RawFinOuterProductDivergence_integrable U V k).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 * ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hDiv.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 * ‖h3RawFinOuterProductDivergence U V k ξ‖ := by
    filter_upwards with ξ

    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_right
        (norm_h3LerayCoefficient_le_two ξ i k)
        (norm_nonneg _)

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
  unfold h3RawFinOuterProductDivergenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3LerayCoefficient ξ i k *
          h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 * ‖h3RawFinOuterProductDivergence U V k ξ‖ :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- The complete Leray-projected forcing zeroth mass is at most twice the sum
of the three divergence-coordinate zeroth masses. -/
theorem h3RawFinLerayOuterProductDivergenceL1Mass_le_divergenceSum
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceL1Mass U V i
      ≤
    2 * ∑ k : Fin 3,
      h3RawFinOuterProductDivergenceL1Mass U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ => ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      (h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
        U V i k).norm

  have hTarget :=
    (h3RawFinLerayOuterProductDivergence_integrable U V i).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3, mterm k ξ)
        (volume : Measure H3FourierPoint3) :=
    integrable_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
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
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖

    exact hSum

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  have hSumIntegral :
      (∫ ξ : H3FourierPoint3,
          ∑ k : Fin 3, mterm k ξ)
        =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
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
          h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
            U V i k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl

  have hCoeffSum :
      (∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
            U V i k)
        ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceL1Mass U V k := by
    exact
      Finset.sum_le_sum fun k _ =>
        h3LerayCoefficientRawFinOuterProductDivergenceL1Mass_le
          U V i k

  unfold h3RawFinLerayOuterProductDivergenceL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceL1Mass
          U V i k :=
      hSumIntegral
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceL1Mass U V k :=
      hCoeffSum
    _ =
      2 * ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceL1Mass U V k := by
      rw [Finset.mul_sum]

/-- Fully quantitative finite forcing zeroth-mass estimate in terms of
coordinatewise unweighted and second state masses. -/
theorem h3RawFinLerayOuterProductDivergenceL1Mass_le_stateMasses
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
    h3RawFinLerayOuterProductDivergenceL1Mass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j)
              +
              2 *
                (h3SpectralScalarRawFourierSecondMass (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierSecondMass (V j))) := by
  have hLeray :=
    h3RawFinLerayOuterProductDivergenceL1Mass_le_divergenceSum
      U V i

  have hDivBounds :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceL1Mass U V k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionL1Mass
            (U k) (V j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceL1Mass_le
        U V k

  have hDerivativeBounds :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionL1Mass
            (U k) (V j) j
          ≤
        (2 * Real.pi) *
          (h3SpectralScalarRawFourierL1Mass (U k) *
              h3SpectralScalarRawFourierL1Mass (V j)
            +
            2 *
              (h3SpectralScalarRawFourierSecondMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierSecondMass (V j))) := by
    intro k j
    exact
      h3FourierDerivativeRawProductConvolutionL1Mass_le_stateMasses
        (U k) (V j) j (hU2 k) (hV2 j)

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceL1Mass U V k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionL1Mass
            (U k) (V j) j := by
    exact
      Finset.sum_le_sum fun k _ => hDivBounds k

  have hDerivativeSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionL1Mass
            (U k) (V j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j)
              +
              2 *
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
    h3RawFinLerayOuterProductDivergenceL1Mass U V i
        ≤
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceL1Mass U V k :=
      hLeray
    _ ≤
      2 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionL1Mass
              (U k) (V j) j) :=
      mul_le_mul_of_nonneg_left hDivSum hTwo0
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j)
                +
                2 *
                  (h3SpectralScalarRawFourierSecondMass (U k) *
                      h3SpectralScalarRawFourierL1Mass (V j) +
                    h3SpectralScalarRawFourierL1Mass (U k) *
                      h3SpectralScalarRawFourierSecondMass (V j))) :=
      mul_le_mul_of_nonneg_left hDerivativeSum hTwo0

/-- Explicit selected-state zeroth forcing envelope. -/
noncomputable def h3SelectedForcingL1Envelope
    (ν A t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedRestartRawFourierL1Envelope A
            +
            2 *
              (h3SelectedMildSecondMomentEnvelope ν A t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildSecondMomentEnvelope ν A t))

/-- Every selected forcing coordinate has zeroth raw Fourier mass bounded by
the explicit zeroth/second state envelope. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_L1Mass_le
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
    h3RawFinLerayOuterProductDivergenceL1Mass
        (W t) (W t) i
      ≤
    h3SelectedForcingL1Envelope ν A t := by
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
    h3RawFinLerayOuterProductDivergenceL1Mass_le_stateMasses
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
            (h3SpectralScalarRawFourierL1Mass (W t k) *
                h3SpectralScalarRawFourierL1Mass (W t j)
              +
              2 *
                (h3SpectralScalarRawFourierSecondMass (W t k) *
                    h3SpectralScalarRawFourierL1Mass (W t j) +
                  h3SpectralScalarRawFourierL1Mass (W t k) *
                    h3SpectralScalarRawFourierSecondMass (W t j)))
          ≤
        (2 * Real.pi) *
          (h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedRestartRawFourierL1Envelope A
            +
            2 *
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

    have hZero :
        h3SpectralScalarRawFourierL1Mass (W t k) *
            h3SpectralScalarRawFourierL1Mass (W t j)
          ≤
        h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedRestartRawFourierL1Envelope A :=
      mul_le_mul
        (hW0 k)
        (hW0 j)
        hj0
        hM0nonneg

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

    have hSecondSum :=
      add_le_add hLeft hRight

    have hSecond :
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
      mul_le_mul_of_nonneg_left hSecondSum (by norm_num)

    have hInside :=
      add_le_add hZero hSecond

    exact
      mul_le_mul_of_nonneg_left hInside (by positivity)

  have hSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3SpectralScalarRawFourierL1Mass (W t k) *
                h3SpectralScalarRawFourierL1Mass (W t j)
              +
              2 *
                (h3SpectralScalarRawFourierSecondMass (W t k) *
                    h3SpectralScalarRawFourierL1Mass (W t j) +
                  h3SpectralScalarRawFourierL1Mass (W t k) *
                    h3SpectralScalarRawFourierSecondMass (W t j))))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedRestartRawFourierL1Envelope A
              +
              2 *
                (h3SelectedMildSecondMomentEnvelope ν A t *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildSecondMomentEnvelope ν A t)) := by
    exact
      Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ =>
          hTerm k j

  unfold h3SelectedForcingL1Envelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum (by norm_num))

end
end Euclidean
end Bridge
end PrimeTensor
