import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentDerivative

/-!
# Fréchet endpoint induction: generic nonlinear forcing moments

This file closes the nonlinear half of the moment induction at an arbitrary
nonnegative real exponent `q`.

The generic derivative theorem already gives

    M_{q+1}(F * G)  ->  M_q(D_j(F * G)).

Here we perform the finite-dimensional bookkeeping once and for all:

* sum the three derivative-convolution terms into one divergence coordinate;
* pass the divergence coordinates through the bounded Leray coefficients;
* sum the three Leray coordinates.

Consequently, coordinatewise `(q+1)` moments on two vector states imply a
`q` moment on every coordinate of the complete Leray-projected quadratic
forcing.  No further Fourier regularity is spent.

This replaces every future named `ForcingMass` checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentForcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Generic `q`-moment mass of one finite outer-product divergence coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceMomentMass
    (q : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierMomentWeight q ξ *
      ‖h3RawFinOuterProductDivergence U V i ξ‖

/-- Generic `q`-moment mass of one complete Leray-divergence forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceMomentMass
    (q : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierMomentWeight q ξ *
      ‖h3RawFinLerayOuterProductDivergence U V i ξ‖

/-- Finite outer-product divergence preserves a generic `q` moment when all
three scalar derivative-convolution terms have that moment. -/
theorem h3RawFinOuterProductDivergence_moment_integrable_of_derivatives
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDeriv :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
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
            h3FourierMomentWeight q ξ * ‖term j ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [term]
    exact hDeriv j

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ j : Fin 3,
            h3FourierMomentWeight q ξ * ‖term j ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hq).aestronglyMeasurable.mul
      (h3RawFinOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hTargetNonneg :
      0 ≤
        h3FourierMomentWeight q ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ j : Fin 3,
          h3FourierMomentWeight q ξ * ‖term j ξ‖ := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg hw (norm_nonneg _)

  have hSum :
      ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3, ‖term j ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

  have hBound :
      h3FourierMomentWeight q ξ *
          ‖h3RawFinOuterProductDivergence U V i ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierMomentWeight q ξ * ‖term j ξ‖ := by
    unfold h3RawFinOuterProductDivergence
    change
      h3FourierMomentWeight q ξ *
          ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierMomentWeight q ξ * ‖term j ξ‖

    calc
      h3FourierMomentWeight q ξ *
          ‖∑ j : Fin 3, term j ξ‖
          ≤
        h3FourierMomentWeight q ξ *
          ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ j : Fin 3,
          h3FourierMomentWeight q ξ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The generic divergence mass is bounded by the sum of its three scalar
derivative-convolution masses. -/
theorem h3RawFinOuterProductDivergenceMomentMass_le
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDeriv :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinOuterProductDivergenceMomentMass q U V i
      ≤
    ∑ j : Fin 3,
      h3FourierDerivativeRawProductConvolutionMomentMass
        q (U i) (V j) j := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun j ξ =>
      h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution (U i) (V j) ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun j ξ =>
      h3FourierMomentWeight q ξ * ‖term j ξ‖

  have hTerm :
      ∀ j : Fin 3,
        Integrable
          (mterm j)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [mterm, term]
    exact hDeriv j

  have hTarget :=
    h3RawFinOuterProductDivergence_moment_integrable_of_derivatives
      hq U V i hDeriv

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
        h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V i ξ‖
          ≤
        ∑ j : Fin 3, mterm j ξ := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    have hSum :
        ‖∑ j : Fin 3, term j ξ‖
          ≤
        ∑ j : Fin 3, ‖term j ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun j => term j ξ)

    unfold h3RawFinOuterProductDivergence
    change
      h3FourierMomentWeight q ξ *
          ‖∑ j : Fin 3, term j ξ‖
        ≤
      ∑ j : Fin 3,
        h3FourierMomentWeight q ξ * ‖term j ξ‖

    calc
      h3FourierMomentWeight q ξ *
          ‖∑ j : Fin 3, term j ξ‖
          ≤
        h3FourierMomentWeight q ξ *
          ∑ j : Fin 3, ‖term j ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ j : Fin 3,
          h3FourierMomentWeight q ξ * ‖term j ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceMomentMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
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
        h3FourierDerivativeRawProductConvolutionMomentMass
          q (U i) (V j) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

/-- A bounded Leray coefficient preserves a generic `q` moment of one
divergence coordinate. -/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_moment_integrable
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hComplex :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
      U V i k

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hq).aestronglyMeasurable.mul
      hComplex.aestronglyMeasurable.norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv.const_mul 2

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hTargetNonneg :
      0 ≤
        h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        2 *
          (h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    positivity

  have hBound :
      h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      2 *
        (h3FourierMomentWeight q ξ *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    calc
      h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        h3FourierMomentWeight q ξ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierMomentWeight q ξ *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          hw
      _ =
        2 *
          (h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- One bounded Leray coefficient costs at most a factor `2` in generic
`q`-moment mass. -/
theorem integral_moment_h3LerayCoefficient_mul_rawFinOuterProductDivergence_le
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
      ≤
    2 * h3RawFinOuterProductDivergenceMomentMass q U V k := by
  have hTarget :=
    h3LerayCoefficient_mul_rawFinOuterProductDivergence_moment_integrable
      hq U V i k hDiv

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          2 *
            (h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hDiv.const_mul 2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        h3FourierMomentWeight q ξ *
            ‖h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ‖
          ≤
        2 *
          (h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    calc
      h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖
          =
        h3FourierMomentWeight q ξ *
          (‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        rw [norm_mul]
      _ ≤
        h3FourierMomentWeight q ξ *
          (2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_h3LerayCoefficient_le_two ξ i k)
            (norm_nonneg _))
          hw
      _ =
        2 *
          (h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinOuterProductDivergenceMomentMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        2 *
          (h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      hIntegral
    _ =
      2 *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      rw [integral_const_mul]

/-- The complete finite Leray projection preserves a generic `q` moment of all
divergence coordinates. -/
theorem h3RawFinLerayOuterProductDivergence_moment_integrable_of_divergence
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
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
            h3FourierMomentWeight q ξ * ‖term k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_moment_integrable
        hq U V i k (hDiv k)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∑ k : Fin 3,
            h3FourierMomentWeight q ξ * ‖term k ξ‖)
        (volume : Measure H3FourierPoint3) :=
    integrable_finset_sum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hq).aestronglyMeasurable.mul
      (h3RawFinLerayOuterProductDivergence_integrable U V i).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hTargetNonneg :
      0 ≤
        h3FourierMomentWeight q ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        ∑ k : Fin 3,
          h3FourierMomentWeight q ξ * ‖term k ξ‖ := by
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg hw (norm_nonneg _)

  have hSum :
      ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3, ‖term k ξ‖ :=
    norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

  have hBound :
      h3FourierMomentWeight q ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierMomentWeight q ξ * ‖term k ξ‖ := by
    unfold h3RawFinLerayOuterProductDivergence
    change
      h3FourierMomentWeight q ξ *
          ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierMomentWeight q ξ * ‖term k ξ‖

    calc
      h3FourierMomentWeight q ξ *
          ‖∑ k : Fin 3, term k ξ‖
          ≤
        h3FourierMomentWeight q ξ *
          ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ k : Fin 3,
          h3FourierMomentWeight q ξ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- The complete Leray-projected generic `q` mass is at most twice the sum of
the three divergence-coordinate masses. -/
theorem h3RawFinLerayOuterProductDivergenceMomentMass_le
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3)) :
    h3RawFinLerayOuterProductDivergenceMomentMass q U V i
      ≤
    2 *
      ∑ k : Fin 3,
        h3RawFinOuterProductDivergenceMomentMass q U V k := by
  let term : Fin 3 → H3FourierPoint3 → ℂ :=
    fun k ξ =>
      h3LerayCoefficient ξ i k *
        h3RawFinOuterProductDivergence U V k ξ

  let mterm : Fin 3 → H3FourierPoint3 → ℝ :=
    fun k ξ =>
      h3FourierMomentWeight q ξ * ‖term k ξ‖

  have hTerm :
      ∀ k : Fin 3,
        Integrable
          (mterm k)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [mterm, term]
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_moment_integrable
        hq U V i k (hDiv k)

  have hTarget :=
    h3RawFinLerayOuterProductDivergence_moment_integrable_of_divergence
      hq U V i hDiv

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
        h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
          ≤
        ∑ k : Fin 3, mterm k ξ := by
    filter_upwards with ξ

    have hw :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    have hSum :
        ‖∑ k : Fin 3, term k ξ‖
          ≤
        ∑ k : Fin 3, ‖term k ξ‖ :=
      norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k => term k ξ)

    unfold h3RawFinLerayOuterProductDivergence
    change
      h3FourierMomentWeight q ξ *
          ‖∑ k : Fin 3, term k ξ‖
        ≤
      ∑ k : Fin 3,
        h3FourierMomentWeight q ξ * ‖term k ξ‖

    calc
      h3FourierMomentWeight q ξ *
          ‖∑ k : Fin 3, term k ξ‖
          ≤
        h3FourierMomentWeight q ξ *
          ∑ k : Fin 3, ‖term k ξ‖ :=
        mul_le_mul_of_nonneg_left hSum hw
      _ =
        ∑ k : Fin 3,
          h3FourierMomentWeight q ξ * ‖term k ξ‖ := by
        rw [Finset.mul_sum]

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawFinLerayOuterProductDivergenceMomentMass

  have hTermIntegral :
      ∀ k : Fin 3,
        (∫ ξ : H3FourierPoint3, mterm k ξ)
          ≤
        2 * h3RawFinOuterProductDivergenceMomentMass q U V k := by
    intro k
    dsimp only [mterm, term]
    exact
      integral_moment_h3LerayCoefficient_mul_rawFinOuterProductDivergence_le
        hq U V i k (hDiv k)

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ∑ k : Fin 3, mterm k ξ :=
      hIntegral
    _ =
      ∑ k : Fin 3,
        ∫ ξ : H3FourierPoint3, mterm k ξ := by
      simpa using
        (MeasureTheory.integral_finsetSum
          (Finset.univ : Finset (Fin 3))
          (fun k _ => hTerm k))
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceMomentMass q U V k := by
      exact
        Finset.sum_le_sum fun k _ =>
          hTermIntegral k
    _ =
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceMomentMass q U V k := by
      rw [Finset.mul_sum]

/-- Coordinatewise `(q+1)` moments on two vector states imply an integrable
generic `q` moment for every coordinate of the complete nonlinear forcing. -/
theorem h3RawFinLerayOuterProductDivergence_moment_integrable_of_nextMoments
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable (q + 1) (U k))
    (hV :
      ∀ j : Fin 3,
        H3RawFourierMomentIntegrable (q + 1) (V j))
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight q ξ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k

    have hDeriv :
        ∀ j : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              h3FourierMomentWeight q ξ *
                ‖h3FourierDerivativeSymbol j ξ *
                  h3RawProductConvolution (U k) (V j) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro j

      have hqNext : 0 ≤ q + 1 := by
        linarith

      have hConv :=
        h3RawProductConvolution_moment_integrable_of
          hqNext (U k) (V j) (hU k) (hV j)

      exact
        h3FourierDerivative_mul_rawProductConvolution_moment_integrable_of_nextMoment
          hq (U k) (V j) j hConv

    exact
      h3RawFinOuterProductDivergence_moment_integrable_of_derivatives
        hq U V k hDeriv

  exact
    h3RawFinLerayOuterProductDivergence_moment_integrable_of_divergence
      hq U V i hDiv

/-- Fully quantitative generic nonlinear forcing estimate from coordinatewise
`(q+1)` state moments. -/
theorem h3RawFinLerayOuterProductDivergenceMomentMass_le_stateMoments
    {q : ℝ}
    (hq : 0 ≤ q)
    (U V : H3SpectralFinVectorState)
    (hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable (q + 1) (U k))
    (hV :
      ∀ j : Fin 3,
        H3RawFourierMomentIntegrable (q + 1) (V j))
    (i : Fin 3) :
    h3RawFinLerayOuterProductDivergenceMomentMass q U V i
      ≤
    2 *
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierMomentSplitCoefficient (q + 1) *
              (h3SpectralScalarRawFourierMomentMass (q + 1) (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierMomentMass (q + 1) (V j))) := by
  have hDiv :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinOuterProductDivergence U V k ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k

    have hDeriv :
        ∀ j : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              h3FourierMomentWeight q ξ *
                ‖h3FourierDerivativeSymbol j ξ *
                  h3RawProductConvolution (U k) (V j) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro j

      have hqNext : 0 ≤ q + 1 := by
        linarith

      have hConv :=
        h3RawProductConvolution_moment_integrable_of
          hqNext (U k) (V j) (hU k) (hV j)

      exact
        h3FourierDerivative_mul_rawProductConvolution_moment_integrable_of_nextMoment
          hq (U k) (V j) j hConv

    exact
      h3RawFinOuterProductDivergence_moment_integrable_of_derivatives
        hq U V k hDeriv

  have hLeray :=
    h3RawFinLerayOuterProductDivergenceMomentMass_le
      hq U V i hDiv

  have hOuter :
      ∀ k : Fin 3,
        h3RawFinOuterProductDivergenceMomentMass q U V k
          ≤
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierMomentSplitCoefficient (q + 1) *
              (h3SpectralScalarRawFourierMomentMass (q + 1) (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierMomentMass (q + 1) (V j))) := by
    intro k

    have hDeriv :
        ∀ j : Fin 3,
          Integrable
            (fun ξ : H3FourierPoint3 =>
              h3FourierMomentWeight q ξ *
                ‖h3FourierDerivativeSymbol j ξ *
                  h3RawProductConvolution (U k) (V j) ξ‖)
            (volume : Measure H3FourierPoint3) := by
      intro j

      have hqNext : 0 ≤ q + 1 := by
        linarith

      have hConv :=
        h3RawProductConvolution_moment_integrable_of
          hqNext (U k) (V j) (hU k) (hV j)

      exact
        h3FourierDerivative_mul_rawProductConvolution_moment_integrable_of_nextMoment
          hq (U k) (V j) j hConv

    have hOuterBase :=
      h3RawFinOuterProductDivergenceMomentMass_le
        hq U V k hDeriv

    have hEach :
        ∀ j : Fin 3,
          h3FourierDerivativeRawProductConvolutionMomentMass
              q (U k) (V j) j
            ≤
          (2 * Real.pi) *
            (h3FourierMomentSplitCoefficient (q + 1) *
              (h3SpectralScalarRawFourierMomentMass (q + 1) (U k) *
                  h3SpectralScalarRawFourierL1Mass (V j) +
                h3SpectralScalarRawFourierL1Mass (U k) *
                  h3SpectralScalarRawFourierMomentMass (q + 1) (V j))) := by
      intro j
      exact
        h3FourierDerivativeRawProductConvolutionMomentMass_le_stateMasses
          hq (U k) (V j) j (hU k) (hV j)

    exact
      le_trans hOuterBase
        (Finset.sum_le_sum fun j _ => hEach j)

  calc
    h3RawFinLerayOuterProductDivergenceMomentMass q U V i
        ≤
      2 *
        ∑ k : Fin 3,
          h3RawFinOuterProductDivergenceMomentMass q U V k :=
      hLeray
    _ ≤
      2 *
        ∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierMomentSplitCoefficient (q + 1) *
                (h3SpectralScalarRawFourierMomentMass (q + 1) (U k) *
                    h3SpectralScalarRawFourierL1Mass (V j) +
                  h3SpectralScalarRawFourierL1Mass (U k) *
                    h3SpectralScalarRawFourierMomentMass (q + 1) (V j))) := by
      exact
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k _ => hOuter k)
          (by norm_num)

end
end Euclidean
end Bridge
end PrimeTensor
