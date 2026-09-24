import PrimeTensor.Fluid.Vorticity.Continuation.H3.Selected.Forcing.Radial.L2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Weighted.Convolution.Majorant.Local
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.C0.Bridge
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Fourier L∞ ceiling for the unheated H³ nonlinear forcing

`H3PathSelectedForcingRadialL2` proved arbitrary finite radial Fourier `L²`
regularity of the selected positive-time nonlinear forcing.

For the next temporal-integrability step we also need a frequency-independent
pointwise ceiling.  That ceiling is already latent in the H³ algebra:

* the exact weighted product convolution
      W₃(ξ) (F̂ * Ĝ)(ξ)
  is dominated by two scalar `L² × L² -> L∞` Young majorants;
* one Fourier derivative after deweighting costs at most `2π`;
* the outer-product divergence and Leray projection are finite sums, with
  every Leray coefficient bounded by `2`.

This file packages those bounds without collapsing them to a coarse numerical
constant.  The resulting finite-sum envelope depends only on the two H³
spectral input states and is independent of output frequency.

That is the pointwise half of the square estimate

    weighted-L²² <= forcing-L∞ * weighted-L¹,

which will be combined next with the uniform natural-moment slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingFourierLinf
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Scalar weighted product-convolution ceiling -/

/-- Frequency-independent `L∞` ceiling supplied by the two endpoint
`L² × L² -> L∞` Young majorants. -/
noncomputable def h3WeightedRawProductConvolutionLinfBound
    (F G : H3SpectralScalarState) : ℝ :=
  8 *
    (h3FirstYoungMajorantLinfBound F G
      +
     h3SecondYoungMajorantLinfBound F G)

theorem h3WeightedRawProductConvolutionLinfBound_nonneg
    (F G : H3SpectralScalarState) :
    0 ≤ h3WeightedRawProductConvolutionLinfBound F G := by
  unfold h3WeightedRawProductConvolutionLinfBound
  have hFirst :
      0 ≤ h3FirstYoungMajorantLinfBound F G := by
    unfold h3FirstYoungMajorantLinfBound
    positivity
  have hSecond :
      0 ≤ h3SecondYoungMajorantLinfBound F G := by
    unfold h3SecondYoungMajorantLinfBound
    positivity
  positivity

/-- The exact weighted raw product convolution is bounded pointwise by the
frequency-independent Young ceiling. -/
theorem norm_h3WeightedRawProductConvolution_le_linfBound
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3WeightedRawProductConvolution F G ξ‖
      ≤
    h3WeightedRawProductConvolutionLinfBound F G := by

  have hWeighted :=
    norm_h3WeightedRawProductConvolution_le_majorant
      F G ξ

  have hFirst :=
    h3FirstYoungMajorant_le_linfBound
      F G ξ

  have hSecond :=
    h3SecondYoungMajorant_le_linfBound
      F G ξ

  calc
    ‖h3WeightedRawProductConvolution F G ξ‖
        ≤
      h3WeightedYoungMajorant F G ξ :=
      hWeighted
    _ =
      8 *
        (h3FirstYoungMajorant F G ξ
          +
         h3SecondYoungMajorant F G ξ) := by
      rfl
    _ ≤
      8 *
        (h3FirstYoungMajorantLinfBound F G
          +
         h3SecondYoungMajorantLinfBound F G) := by
      exact
        mul_le_mul_of_nonneg_left
          (add_le_add hFirst hSecond)
          (by norm_num)
    _ =
      h3WeightedRawProductConvolutionLinfBound F G := by
      rfl

/-! ## Spend the one divergence derivative -/

/-- Frequency-independent ceiling for one derivative of a raw scalar product
convolution. -/
noncomputable def h3FourierDerivativeRawProductConvolutionLinfBound
    (F G : H3SpectralScalarState) : ℝ :=
  (2 * Real.pi) *
    h3WeightedRawProductConvolutionLinfBound F G

theorem h3FourierDerivativeRawProductConvolutionLinfBound_nonneg
    (F G : H3SpectralScalarState) :
    0 ≤ h3FourierDerivativeRawProductConvolutionLinfBound F G := by
  unfold h3FourierDerivativeRawProductConvolutionLinfBound
  exact
    mul_nonneg
      (by positivity)
      (h3WeightedRawProductConvolutionLinfBound_nonneg F G)

/-- One Fourier derivative of the exact raw product convolution is uniformly
bounded in frequency. -/
theorem norm_h3FourierDerivative_mul_rawProductConvolution_le_linfBound
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3FourierDerivativeSymbol j ξ *
        h3RawProductConvolution F G ξ‖
      ≤
    h3FourierDerivativeRawProductConvolutionLinfBound F G := by

  have hInv0 :
      0 ≤ h3SobolevFrequencyWeightInv ξ := by
    unfold h3SobolevFrequencyWeightInv
    exact
      inv_nonneg.mpr
        (h3SobolevFrequencyWeight_pos ξ).le

  have hTwoPi :
      0 ≤ 2 * Real.pi := by
    positivity

  have hDerivInv :
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
        ≤
      2 * Real.pi := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖ *
          h3SobolevFrequencyWeightInv ξ
          ≤
        h3FourierGradientMagnitude ξ *
          h3SobolevFrequencyWeightInv ξ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude
            j ξ)
          hInv0
      _ =
        (2 * Real.pi) *
          h3SobolevFrequencyFirstMomentInv ξ := by
        unfold
          h3FourierGradientMagnitude
          h3SobolevFrequencyFirstMomentInv
        ring
      _ ≤
        (2 * Real.pi) * 1 :=
        mul_le_mul_of_nonneg_left
          (h3SobolevFrequencyFirstMomentInv_le_one ξ)
          hTwoPi
      _ = 2 * Real.pi := by
        ring

  have hRawEq :
      h3RawProductConvolution F G ξ
        =
      h3SobolevFrequencyWeightInvComplex ξ *
        h3WeightedRawProductConvolution F G ξ := by
    unfold h3WeightedRawProductConvolution
    rw [
      ← mul_assoc,
      h3SobolevFrequencyWeightInvComplex_mul_weight,
      one_mul
    ]

  rw [hRawEq]
  rw [← mul_assoc]
  rw [norm_mul, norm_mul]

  unfold h3SobolevFrequencyWeightInvComplex
  rw [
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hInv0
  ]

  calc
    (‖h3FourierDerivativeSymbol j ξ‖ *
        h3SobolevFrequencyWeightInv ξ) *
        ‖h3WeightedRawProductConvolution F G ξ‖
        ≤
      (2 * Real.pi) *
        ‖h3WeightedRawProductConvolution F G ξ‖ :=
      mul_le_mul_of_nonneg_right
        hDerivInv
        (norm_nonneg _)
    _ ≤
      (2 * Real.pi) *
        h3WeightedRawProductConvolutionLinfBound F G :=
      mul_le_mul_of_nonneg_left
        (norm_h3WeightedRawProductConvolution_le_linfBound
          F G ξ)
        hTwoPi
    _ =
      h3FourierDerivativeRawProductConvolutionLinfBound F G := by
      rfl

/-! ## Finite outer-product divergence ceiling -/

/-- Frequency-independent ceiling for one finite outer-product divergence
coordinate. -/
noncomputable def h3RawFinOuterProductDivergenceLinfBound
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) : ℝ :=
  ∑ j : Fin 3,
    h3FourierDerivativeRawProductConvolutionLinfBound
      (U i) (V j)

theorem h3RawFinOuterProductDivergenceLinfBound_nonneg
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    0 ≤ h3RawFinOuterProductDivergenceLinfBound U V i := by
  unfold h3RawFinOuterProductDivergenceLinfBound
  exact
    Finset.sum_nonneg fun j _ =>
      h3FourierDerivativeRawProductConvolutionLinfBound_nonneg
        (U i) (V j)

/-- The finite outer-product divergence is uniformly bounded in frequency by
the sum of its three scalar derivative-convolution ceilings. -/
theorem norm_h3RawFinOuterProductDivergence_le_linfBound
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinOuterProductDivergence U V i ξ‖
      ≤
    h3RawFinOuterProductDivergenceLinfBound U V i := by

  unfold
    h3RawFinOuterProductDivergence
    h3RawFinOuterProductDivergenceLinfBound

  calc
    ‖∑ j : Fin 3,
        h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution (U i) (V j) ξ‖
        ≤
      ∑ j : Fin 3,
        ‖h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution (U i) (V j) ξ‖ :=
      norm_sum_le
        (Finset.univ : Finset (Fin 3))
        (fun j =>
          h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (U i) (V j) ξ)
    _ ≤
      ∑ j : Fin 3,
        h3FourierDerivativeRawProductConvolutionLinfBound
          (U i) (V j) := by
      exact
        Finset.sum_le_sum fun j _ =>
          norm_h3FourierDerivative_mul_rawProductConvolution_le_linfBound
            (U i) (V j) j ξ

/-! ## Complete Leray forcing ceiling -/

/-- Frequency-independent ceiling for one complete finite Leray forcing
coordinate. -/
noncomputable def h3RawFinLerayOuterProductDivergenceLinfBound
    (U V : H3SpectralFinVectorState) : ℝ :=
  ∑ k : Fin 3,
    2 * h3RawFinOuterProductDivergenceLinfBound U V k

theorem h3RawFinLerayOuterProductDivergenceLinfBound_nonneg
    (U V : H3SpectralFinVectorState) :
    0 ≤ h3RawFinLerayOuterProductDivergenceLinfBound U V := by
  unfold h3RawFinLerayOuterProductDivergenceLinfBound
  exact
    Finset.sum_nonneg fun k _ =>
      mul_nonneg
        (by norm_num)
        (h3RawFinOuterProductDivergenceLinfBound_nonneg U V k)

/--
Every complete finite Leray-divergence forcing coordinate is bounded uniformly
over Fourier frequency by one finite scalar envelope depending only on the two
H³ spectral input states.
-/
theorem norm_h3RawFinLerayOuterProductDivergence_le_linfBound
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
      ≤
    h3RawFinLerayOuterProductDivergenceLinfBound U V := by

  unfold
    h3RawFinLerayOuterProductDivergence
    h3RawFinLerayOuterProductDivergenceLinfBound

  calc
    ‖∑ k : Fin 3,
        h3LerayCoefficient ξ i k *
          h3RawFinOuterProductDivergence U V k ξ‖
        ≤
      ∑ k : Fin 3,
        ‖h3LerayCoefficient ξ i k *
          h3RawFinOuterProductDivergence U V k ξ‖ :=
      norm_sum_le
        (Finset.univ : Finset (Fin 3))
        (fun k =>
          h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ)
    _ ≤
      ∑ k : Fin 3,
        2 * h3RawFinOuterProductDivergenceLinfBound U V k := by
      apply Finset.sum_le_sum
      intro k hk

      rw [norm_mul]

      have hCoeff :=
        norm_h3LerayCoefficient_le_two ξ i k

      have hDiv :=
        norm_h3RawFinOuterProductDivergence_le_linfBound
          U V k ξ

      calc
        ‖h3LerayCoefficient ξ i k‖ *
            ‖h3RawFinOuterProductDivergence U V k ξ‖
            ≤
          2 *
            ‖h3RawFinOuterProductDivergence U V k ξ‖ :=
          mul_le_mul_of_nonneg_right
            hCoeff
            (norm_nonneg _)
        _ ≤
          2 *
            h3RawFinOuterProductDivergenceLinfBound U V k :=
          mul_le_mul_of_nonneg_left
            hDiv
            (by norm_num)

/-! ## Selected-path specialization -/

/--
The selected positive-time nonlinear forcing inherits the same
frequency-independent ceiling at each source time.  No heat lag is used.
-/
theorem norm_h3RawFinLerayOuterProductDivergence_selectedRestart_le_linfBound
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergence
        (W s) (W s) i ξ‖
      ≤
    h3RawFinLerayOuterProductDivergenceLinfBound
      (W s) (W s) := by
  dsimp only
  exact
    norm_h3RawFinLerayOuterProductDivergence_le_linfBound
      _ _ i ξ

end

end Euclidean
end Bridge
end PrimeTensor
