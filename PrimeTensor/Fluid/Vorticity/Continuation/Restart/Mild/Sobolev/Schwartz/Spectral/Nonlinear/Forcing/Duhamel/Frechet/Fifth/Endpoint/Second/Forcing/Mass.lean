import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Third.Convolution.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.First.Forcing.Mass

/-!
# Fifth Fréchet endpoint: quantitative second forcing moment

The fourth endpoint closes a quantitative selected-state cubic Fourier moment.
`ThirdConvolutionMass` propagates that through the exact raw quadratic
convolution:

    m₃(F * G)
      ≤
    4 (m₃(F)m₀(G) + m₀(F)m₃(G)).

The nonlinear forcing spends one Fourier power on divergence.  This file lifts
the established first-forcing argument by one order:

* cubic convolution moment -> derivative second moment;
* finite outer-product divergence second moment;
* bounded Leray projection second moment;
* selected-state quantitative forcing envelope.

The resulting selected forcing bound is the fifth-layer analogue of
`h3SelectedForcingFirstMomentEnvelope`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointSecondForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Second raw Fourier mass after one derivative hits one exact raw product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionSecondMass
    (F G : H3SpectralScalarState)
    (j : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖

/-- Spending one Fourier derivative on an integrable cubic convolution leaves
an integrable second moment. -/
theorem h3FourierDerivative_mul_rawProductConvolution_secondMoment_integrable_of_thirdMoment
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3FourierDerivative_mul_rawProductConvolution_integrable F G j

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 2).aestronglyMeasurable).mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv3.const_mul (2 * Real.pi)

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hDerivative :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    simpa [h3FourierGradientMagnitude] using
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖) := by
    positivity

  have hBound :
      ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        (‖ξ‖ ^ 3 *
          ‖h3RawProductConvolution F G ξ‖) := by
    calc
      ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 2 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 2 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One derivative costs at most `(2π)` times the cubic raw convolution mass. -/
theorem h3FourierDerivativeRawProductConvolutionSecondMass_le
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionSecondMass F G j
      ≤
    (2 * Real.pi) *
      h3RawProductConvolutionThirdMass F G := by
  have hTarget :=
    h3FourierDerivative_mul_rawProductConvolution_secondMoment_integrable_of_thirdMoment
      F G j hConv3

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hConv3.const_mul (2 * Real.pi)

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 2 *
            ‖h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ‖
          ≤
        (2 * Real.pi) *
          (‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖) := by
    filter_upwards with ξ

    have hDerivative :
        ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa [h3FourierGradientMagnitude] using
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

    calc
      ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖
          =
        ‖ξ‖ ^ 2 *
          (‖h3FourierDerivativeSymbol j ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 2 *
          (((2 * Real.pi) * ‖ξ‖) *
            ‖h3RawProductConvolution F G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDerivative
            (norm_nonneg _))
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3FourierDerivativeRawProductConvolutionSecondMass
  unfold h3RawProductConvolutionThirdMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (2 * Real.pi) *
          (‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (2 * Real.pi) *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_const_mul]

/-- Fully quantitative derivative estimate in terms of cubic and unweighted
state masses. -/
theorem h3FourierDerivativeRawProductConvolutionSecondMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3FourierDerivativeRawProductConvolutionSecondMass F G j
      ≤
    (2 * Real.pi) *
      (h3FourierThirdSplitCoefficient *
        (h3SpectralScalarRawFourierThirdMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierThirdMass G)) := by
  have hConv3 :=
    h3RawProductConvolution_thirdMoment_integrable_of
      F G hF3 hG3

  have hDerivative :=
    h3FourierDerivativeRawProductConvolutionSecondMass_le
      F G j hConv3

  have hConvMass :=
    h3RawProductConvolutionThirdMass_le
      F G hF3 hG3

  exact
    le_trans hDerivative
      (mul_le_mul_of_nonneg_left
        hConvMass
        (by positivity))

/-- Second raw Fourier mass of one finite outer-product divergence coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceSecondMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- Second raw Fourier mass of one Leray coefficient times one divergence
coordinate. -/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ‖

/-- Second raw Fourier mass of one complete finite Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceSecondMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- Generic finite outer-product divergence second-moment propagation from
cubic moments of all scalar raw convolutions. -/
theorem h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv3 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
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
            ‖ξ‖ ^ 2 * ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_secondMoment_integrable_of_thirdMoment
        (U i) (V j) j (hConv3 j)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 2).aestronglyMeasurable).mul
      (h3RawFinOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖h3RawFinOuterProductDivergence U V i ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖ := by
    exact Finset.sum_nonneg fun j _ => by positivity

  have hSum :
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

  have hBound :
      ‖ξ‖ ^ 2 *
          ‖h3RawFinOuterProductDivergence U V i ξ‖
        ≤
      ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖ := by
    unfold h3RawFinOuterProductDivergence
    change
      ‖ξ‖ ^ 2 * ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖
    calc
      ‖ξ‖ ^ 2 * ‖∑ j : Fin 3, term j ξ‖
          ≤
        ‖ξ‖ ^ 2 * ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left
          hSum
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The divergence second mass is bounded by the sum of its three scalar
derivative-convolution second masses. -/
theorem h3RawFinOuterProductDivergenceSecondMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hConv3 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinOuterProductDivergenceSecondMass U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionSecondMass
        (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ => ‖ξ‖ ^ 2 * ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact
      h3FourierDerivative_mul_rawProductConvolution_secondMoment_integrable_of_thirdMoment
        (U i) (V j) j (hConv3 j)

  have hTarget :=
    h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
      U V i hConv3

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
        ‖ξ‖ ^ 2 *
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
      ‖ξ‖ ^ 2 * ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖

    calc
      ‖ξ‖ ^ 2 * ‖∑ j : Fin 3, term j ξ‖
          ≤
        ‖ξ‖ ^ 2 * ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left
          hSum
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        ∑ j : Fin 3, ‖ξ‖ ^ 2 * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
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
        h3FourierDerivativeRawProductConvolutionSecondMass
          (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- A bounded Leray coefficient preserves the second raw Fourier moment of one
divergence coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_secondMoment_integrable
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 2).aestronglyMeasurable).mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv2.const_mul 2

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    positivity

  have hBound :
      ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 *
        (‖ξ‖ ^ 2 *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    calc
      ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        ‖ξ‖ ^ 2 *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 2 *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One bounded Leray coefficient costs at most a factor `2` in second mass. -/
theorem h3LerayCoefficientRawFinOuterProductDivergenceSecondMass_le
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
        U V i k
      ≤
    2 * h3RawFinOuterProductDivergenceSecondMass U V k := by
  have hTarget :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_secondMoment_integrable
      U V i k hDiv2

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv2.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ ^ 2 *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    filter_upwards with ξ

    calc
      ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        ‖ξ‖ ^ 2 *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        ‖ξ‖ ^ 2 *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
  unfold h3RawFinOuterProductDivergenceSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 *
          (‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- Generic finite Leray projection preserves the second raw Fourier moment of
all raw divergence coordinates. -/
theorem h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_divergenceSecond
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
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
            ‖ξ‖ ^ 2 * ‖term k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_secondMoment_integrable
        U V i k (hDiv2 k)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    ((continuous_norm.pow 2).aestronglyMeasurable).mul
      (h3RawFinLerayOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hTargetNonneg :
      0 ≤
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
    positivity

  have hMajorNonneg :
      0 ≤
        ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖ := by
    exact Finset.sum_nonneg fun k _ => by positivity

  have hSum :
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

  have hBound :
      ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergence
    change
      ‖ξ‖ ^ 2 * ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖
    calc
      ‖ξ‖ ^ 2 * ‖∑ k : Fin 3, term k ξ‖
          ≤
        ‖ξ‖ ^ 2 * ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left
          hSum
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The complete Leray-projected forcing second mass is at most twice the sum
of the three divergence-coordinate second masses. -/
theorem h3RawFinLerayOuterProductDivergenceSecondMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceSecondMass U V i
      ≤
    2 * ∑ k : Fin 3,
      h3RawFinOuterProductDivergenceSecondMass U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ => ‖ξ‖ ^ 2 * ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_secondMoment_integrable
        U V i k (hDiv2 k)

  have hTarget :=
    h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_divergenceSecond
      U V i hDiv2

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
        ‖ξ‖ ^ 2 *
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
      ‖ξ‖ ^ 2 * ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖

    calc
      ‖ξ‖ ^ 2 * ‖∑ k : Fin 3, term k ξ‖
          ≤
        ‖ξ‖ ^ 2 * ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left
          hSum
          (pow_nonneg (norm_nonneg ξ) 2)
      _ =
        ∑ k : Fin 3, ‖ξ‖ ^ 2 * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  have hSumIntegral :
      (∫ ξ : H3FourierPoint3,
          ∑ k : Fin 3, mterm k ξ)
        =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
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
          h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
            U V i k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl

  have hCoeffSum :
      (∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
            U V i k)
        ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceSecondMass U V k :=
    Finset.sum_le_sum fun k _ =>
      h3LerayCoefficientRawFinOuterProductDivergenceSecondMass_le
        U V i k (hDiv2 k)

  unfold h3RawFinLerayOuterProductDivergenceSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceSecondMass
          U V i k :=
      hSumIntegral
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceSecondMass U V k :=
      hCoeffSum
    _ =
      2 * ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceSecondMass U V k := by
      rw [Finset.mul_sum]

/-- Fully quantitative finite forcing estimate in terms of coordinatewise
unweighted and cubic state masses. -/
theorem h3RawFinLerayOuterProductDivergenceSecondMass_le_stateMasses
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (U k) ξ‖)
          (volume : Measure H3FourierPoint3))
    (hV3 :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceSecondMass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierThirdMass (V j))) := by
  have hConv3 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (U k) (V j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_thirdMoment_integrable_of
        (U k) (V j) (hU3 k) (hV3 j)

  have hDiv2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
        U V k (hConv3 k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceSecondMass_le
      U V i hDiv2

  have hDivBounds :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceSecondMass U V k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionSecondMass
            (U k) (V j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceSecondMass_le
        U V k (hConv3 k)

  have hDerivativeBounds :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionSecondMass
            (U k) (V j) j
          ≤
        (2 * Real.pi) *
          (h3FourierThirdSplitCoefficient *
            (h3SpectralScalarRawFourierThirdMass (U k) *
                h3SpectralScalarRawFourierL1Mass (V j) +
              h3SpectralScalarRawFourierL1Mass (U k) *
                h3SpectralScalarRawFourierThirdMass (V j))) := by
    intro k j
    exact
      h3FourierDerivativeRawProductConvolutionSecondMass_le_stateMasses
        (U k) (V j) j (hU3 k) (hV3 j)

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceSecondMass U V k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionSecondMass
            (U k) (V j) j :=
    Finset.sum_le_sum fun k _ => hDivBounds k

  have hDerivativeSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionSecondMass
            (U k) (V j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierThirdMass (V j))) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hDerivativeBounds k j

  calc
    h3RawFinLerayOuterProductDivergenceSecondMass U V i
        ≤
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceSecondMass U V k :=
      hLeray
    _ ≤
      2 *
        (∑ k : Fin 3,
          ∑ j : Fin 3,
            h3FourierDerivativeRawProductConvolutionSecondMass
              (U k) (V j) j) :=
      mul_le_mul_of_nonneg_left hDivSum (by norm_num)
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SpectralScalarRawFourierThirdMass (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierThirdMass (V j))) :=
      mul_le_mul_of_nonneg_left hDerivativeSum (by norm_num)

/-- Explicit selected-state second forcing envelope. -/
noncomputable def h3SelectedForcingSecondMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (h3FourierThirdSplitCoefficient *
            (h3SelectedMildThirdMomentEnvelope ν A t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildThirdMomentEnvelope ν A t))

/-- The selected nonlinear forcing has an integrable second raw Fourier moment
at every positive time in the restart interval. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
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
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR k

  have hConv3 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (W t k) (W t j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_thirdMoment_integrable_of
        (W t k) (W t j) (hW3 k) (hW3 j)

  have hDiv2 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 2 *
              ‖h3RawFinOuterProductDivergence (W t) (W t) k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
        (W t) (W t) k (hConv3 k)

  exact
    h3RawFinLerayOuterProductDivergence_secondMoment_integrable_of_divergenceSecond
      (W t) (W t) i hDiv2

/-- Every selected forcing coordinate has its second raw Fourier mass bounded
by the explicit zeroth/cubic state envelope. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le
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
    h3RawFinLerayOuterProductDivergenceSecondMass
        (W t) (W t) i
      ≤
    h3SelectedForcingSecondMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR k

  have hBase :=
    h3RawFinLerayOuterProductDivergenceSecondMass_le_stateMasses
      (W t) (W t) i hW3 hW3

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

  have hWm3 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierThirdMass (W t k)
          ≤
        h3SelectedMildThirdMomentEnvelope ν A t := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMass_le
        hν U₀ hA hU₀ ht htR k

  have hM0nonneg :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM3nonneg :
      0 ≤ h3SelectedMildThirdMomentEnvelope ν A t := by
    let k0 : Fin 3 := 0
    have hMass0 :
        0 ≤ h3SpectralScalarRawFourierThirdMass (W t k0) :=
      h3SpectralScalarRawFourierThirdMass_nonneg (W t k0)
    exact le_trans hMass0 (hWm3 k0)

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass (W t k) *
                  h3SpectralScalarRawFourierL1Mass (W t j) +
                h3SpectralScalarRawFourierL1Mass (W t k) *
                  h3SpectralScalarRawFourierThirdMass (W t j)))
          ≤
        (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SelectedMildThirdMomentEnvelope ν A t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildThirdMomentEnvelope ν A t)) := by
    intro k j

    have hk0 :=
      h3SpectralScalarRawFourierL1Mass_nonneg (W t k)
    have hj0 :=
      h3SpectralScalarRawFourierL1Mass_nonneg (W t j)
    have hk3 :=
      h3SpectralScalarRawFourierThirdMass_nonneg (W t k)
    have hj3 :=
      h3SpectralScalarRawFourierThirdMass_nonneg (W t j)

    have hLeft :
        h3SpectralScalarRawFourierThirdMass (W t k) *
            h3SpectralScalarRawFourierL1Mass (W t j)
          ≤
        h3SelectedMildThirdMomentEnvelope ν A t *
          h3SelectedRestartRawFourierL1Envelope A :=
      mul_le_mul
        (hWm3 k)
        (hW0 j)
        hj0
        hM3nonneg

    have hRight :
        h3SpectralScalarRawFourierL1Mass (W t k) *
            h3SpectralScalarRawFourierThirdMass (W t j)
          ≤
        h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildThirdMomentEnvelope ν A t :=
      mul_le_mul
        (hW0 k)
        (hWm3 j)
        hj3
        hM0nonneg

    have hSum :=
      add_le_add hLeft hRight

    have hCoeff0 :
        0 ≤ h3FourierThirdSplitCoefficient := by
      unfold h3FourierThirdSplitCoefficient
      norm_num

    have hWeighted :=
      mul_le_mul_of_nonneg_left hSum hCoeff0

    exact
      mul_le_mul_of_nonneg_left hWeighted (by positivity)

  have hSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SpectralScalarRawFourierThirdMass (W t k) *
                  h3SpectralScalarRawFourierL1Mass (W t j) +
                h3SpectralScalarRawFourierL1Mass (W t k) *
                  h3SpectralScalarRawFourierThirdMass (W t j))))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SelectedMildThirdMomentEnvelope ν A t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildThirdMomentEnvelope ν A t)) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hTerm k j

  unfold h3SelectedForcingSecondMomentEnvelope

  exact
    le_trans hBase
      (mul_le_mul_of_nonneg_left hSum (by norm_num))

end
end Euclidean
end Bridge
end PrimeTensor
