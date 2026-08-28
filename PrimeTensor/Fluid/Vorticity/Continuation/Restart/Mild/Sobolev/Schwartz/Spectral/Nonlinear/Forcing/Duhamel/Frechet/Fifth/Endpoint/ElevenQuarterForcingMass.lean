import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.ElevenQuarterDerivativeMass

/-!
# Fifth Fréchet endpoint: quantitative eleven-quarter forcing mass

`ElevenQuarterDerivativeMass` closes the scalar derivative-convolution step

    m_{11/4}(D_j(F * G))
      ≤
    (2π) m_{15/4}(F * G),

and specializes it to the selected mild state.

This file performs the remaining finite-dimensional bookkeeping:

* sum the three derivative-convolution terms into one outer-product divergence;
* pass each divergence coordinate through the bounded Leray coefficients;
* sum the three Leray coordinates;
* specialize both vector inputs to the selected mild state.

No further Fourier regularity is spent.  The resulting complete selected
nonlinear forcing therefore carries a quantitative `11/4` raw Fourier moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointElevenQuarterForcingMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- `11/4` raw Fourier mass of one finite outer-product divergence coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceElevenQuarterMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierElevenQuarterWeight ξ *
      ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- `11/4` raw Fourier mass of one Leray coefficient times one divergence
coordinate. -/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierElevenQuarterWeight ξ *
      ‖h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ‖

/-- `11/4` raw Fourier mass of one complete finite Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceElevenQuarterMass
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierElevenQuarterWeight ξ *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- Finite outer-product divergence preserves an `11/4` moment when all three
scalar derivative-convolution terms have that moment. -/
theorem h3RawFinOuterProductDivergence_elevenQuarterMoment_integrable_of_derivatives
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDeriv :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierElevenQuarterWeight ξ *
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
            h3FourierElevenQuarterWeight ξ * ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [term]
    exact hDeriv j

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3,
            h3FourierElevenQuarterWeight ξ * ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  have hWeightContinuous :
      Continuous h3FourierElevenQuarterWeight := by
    unfold h3FourierElevenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (11 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawFinOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierElevenQuarterWeight ξ := by
    unfold h3FourierElevenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ j : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term j ξ‖ := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg hw (norm_nonneg _)

  have hSum :
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

  have hBound :
      h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term j ξ‖ := by
    unfold h3RawFinOuterProductDivergence
    change
      h3FourierElevenQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term j ξ‖

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
          ≤
        h3FourierElevenQuarterWeight ξ *
          ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ j : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The divergence `11/4` mass is bounded by the sum of its three scalar
derivative-convolution `11/4` masses. -/
theorem h3RawFinOuterProductDivergenceElevenQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDeriv :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinOuterProductDivergenceElevenQuarterMass U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionElevenQuarterMass
        (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ =>
      h3FourierElevenQuarterWeight ξ * ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact hDeriv j

  have hTarget :=
    h3RawFinOuterProductDivergence_elevenQuarterMoment_integrable_of_derivatives
      U V i hDeriv

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
        h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖
          ≤
        ∑ j : Fin 3, mterm j ξ := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierElevenQuarterWeight ξ := by
      unfold h3FourierElevenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hSum :
        ‖∑ j : Fin 3, term j ξ‖
          ≤
        ∑ j : Fin 3, ‖term j ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

    unfold h3RawFinOuterProductDivergence
    change
      h3FourierElevenQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term j ξ‖

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖∑ j : Fin 3, term j ξ‖
          ≤
        h3FourierElevenQuarterWeight ξ *
          ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ j : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceElevenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ *
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
        h3FourierDerivativeRawProductConvolutionElevenQuarterMass
          (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- A bounded Leray coefficient preserves the `11/4` raw Fourier moment of one
divergence coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_elevenQuarterMoment_integrable
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k

  have hWeightContinuous :
      Continuous h3FourierElevenQuarterWeight := by
    unfold h3FourierElevenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (11 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv11.const_mul 2

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierElevenQuarterWeight ξ := by
    unfold h3FourierElevenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        2 *
          (h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    positivity

  have hBound :
      h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 *
        (h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    calc
      h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        h3FourierElevenQuarterWeight ξ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierElevenQuarterWeight ξ *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          hw
      _ =
        2 *
          (h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One bounded Leray coefficient costs at most a factor `2` in `11/4` mass. -/
theorem h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass U V i k
      ≤
    2 * h3RawFinOuterProductDivergenceElevenQuarterMass U V k := by
  have hTarget :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_elevenQuarterMoment_integrable
      U V i k hDiv11

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv11.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierElevenQuarterWeight ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 *
          (h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierElevenQuarterWeight ξ := by
      unfold h3FourierElevenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        h3FourierElevenQuarterWeight ξ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierElevenQuarterWeight ξ *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          hw
      _ =
        2 *
          (h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
  unfold h3RawFinOuterProductDivergenceElevenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 *
          (h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- The complete finite Leray projection preserves the `11/4` raw Fourier
moment of all divergence coordinates. -/
theorem h3RawFinLerayOuterProductDivergence_elevenQuarterMoment_integrable_of_divergence
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv11 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierElevenQuarterWeight ξ *
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
            h3FourierElevenQuarterWeight ξ * ‖term k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_elevenQuarterMoment_integrable
        U V i k (hDiv11 k)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3,
            h3FourierElevenQuarterWeight ξ * ‖term k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  have hWeightContinuous :
      Continuous h3FourierElevenQuarterWeight := by
    unfold h3FourierElevenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (11 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3RawFinLerayOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierElevenQuarterWeight ξ := by
    unfold h3FourierElevenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤
        h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ k : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term k ξ‖ := by
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg hw (norm_nonneg _)

  have hSum :
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

  have hBound :
      h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term k ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergence
    change
      h3FourierElevenQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term k ξ‖

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
          ≤
        h3FourierElevenQuarterWeight ξ *
          ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ k : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The complete Leray-projected forcing `11/4` mass is at most twice the sum
of the three divergence-coordinate masses. -/
theorem h3RawFinLerayOuterProductDivergenceElevenQuarterMass_le
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv11 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceElevenQuarterMass U V i
      ≤
    2 *
      ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceElevenQuarterMass U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ =>
      h3FourierElevenQuarterWeight ξ * ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_elevenQuarterMoment_integrable
        U V i k (hDiv11 k)

  have hTarget :=
    h3RawFinLerayOuterProductDivergence_elevenQuarterMoment_integrable_of_divergence
      U V i hDiv11

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
        h3FourierElevenQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        ∑ k : Fin 3, mterm k ξ := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierElevenQuarterWeight ξ := by
      unfold h3FourierElevenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hSum :
        ‖∑ k : Fin 3, term k ξ‖
          ≤
        ∑ k : Fin 3, ‖term k ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

    unfold h3RawFinLerayOuterProductDivergence
    change
      h3FourierElevenQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierElevenQuarterWeight ξ * ‖term k ξ‖

    calc
      h3FourierElevenQuarterWeight ξ *
          ‖∑ k : Fin 3, term k ξ‖
          ≤
        h3FourierElevenQuarterWeight ξ *
          ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ k : Fin 3,
          h3FourierElevenQuarterWeight ξ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  have hSumIntegral :
      (∫ ξ : H3FourierPoint3,
          ∑ k : Fin 3, mterm k ξ)
        =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
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
          h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
            U V i k := by
        apply Finset.sum_congr rfl
        intro k _hk
        rfl

  have hCoeffSum :
      (∑ k : Fin 3,
          h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
            U V i k)
        ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceElevenQuarterMass U V k :=
    Finset.sum_le_sum fun k _ =>
      h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass_le
        U V i k (hDiv11 k)

  unfold h3RawFinLerayOuterProductDivergenceElevenQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        h3LerayCoefficientRawFinOuterProductDivergenceElevenQuarterMass
          U V i k :=
      hSumIntegral
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceElevenQuarterMass U V k :=
      hCoeffSum
    _ =
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceElevenQuarterMass U V k := by
      rw [Finset.mul_sum]

/-- Explicit selected forcing `11/4` envelope. -/
noncomputable def h3SelectedForcingElevenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        h3SelectedDerivativeElevenQuarterMomentEnvelope ν A t

/-- Every selected forcing coordinate has an integrable `11/4` raw Fourier
moment. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_elevenQuarterMoment_integrable
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
        h3FourierElevenQuarterWeight ξ *
          ‖h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hDeriv :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (W t k) (W t j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivative_mul_rawProductConvolution_selectedRestart_elevenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR k j

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence (W t) (W t) k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_elevenQuarterMoment_integrable_of_derivatives
        (W t) (W t) k (hDeriv k)

  exact
    h3RawFinLerayOuterProductDivergence_elevenQuarterMoment_integrable_of_divergence
      (W t) (W t) i hDiv

/-- Every selected forcing coordinate has `11/4` raw Fourier mass bounded by
the explicit selected forcing envelope. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_elevenQuarterMass_le
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
    h3RawFinLerayOuterProductDivergenceElevenQuarterMass
        (W t) (W t) i
      ≤
    h3SelectedForcingElevenQuarterMomentEnvelope ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hDeriv :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (W t k) (W t j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivative_mul_rawProductConvolution_selectedRestart_elevenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR k j

  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierElevenQuarterWeight ξ *
              ‖h3RawFinOuterProductDivergence (W t) (W t) k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_elevenQuarterMoment_integrable_of_derivatives
        (W t) (W t) k (hDeriv k)

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceElevenQuarterMass_le
      (W t) (W t) i hDiv

  have hDivBound :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceElevenQuarterMass
            (W t) (W t) k
          ≤
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionElevenQuarterMass
            (W t k) (W t j) j := by
    intro k
    exact
      h3RawFinOuterProductDivergenceElevenQuarterMass_le
        (W t) (W t) k (hDeriv k)

  have hDerivativeBound :
      ∀ k j : Fin 3,
        h3FourierDerivativeRawProductConvolutionElevenQuarterMass
            (W t k) (W t j) j
          ≤
        h3SelectedDerivativeElevenQuarterMomentEnvelope ν A t := by
    intro k j
    dsimp only [W]
    exact
      h3FourierDerivativeRawProductConvolution_selectedRestart_elevenQuarterMass_le
        hν U₀ hA hU₀ ht htR k j

  have hDivSum :
      (∑ k : Fin 3,
          h3RawFinOuterProductDivergenceElevenQuarterMass
            (W t) (W t) k)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionElevenQuarterMass
            (W t k) (W t j) j :=
    Finset.sum_le_sum fun k _ => hDivBound k

  have hDerivativeSum :
      (∑ k : Fin 3,
        ∑ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionElevenQuarterMass
            (W t k) (W t j) j)
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          h3SelectedDerivativeElevenQuarterMomentEnvelope ν A t :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hDerivativeBound k j

  unfold h3SelectedForcingElevenQuarterMomentEnvelope

  exact
    le_trans hLeray
      (mul_le_mul_of_nonneg_left
        (le_trans hDivSum hDerivativeSum)
        (by norm_num))

end
end Euclidean
end Bridge
end PrimeTensor
