import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedDuhamelTailWeightedKernelL2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.Moment.Convolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Raw.Convolution.Continuity

/-!
# Arbitrary radial Fourier L² regularity of the selected nonlinear forcing

The terminal-tail source slices are already spatially `L²` at every finite
radial order after inserting a positive heat lag.  The remaining question is
whether the weighted `L²` norm stays integrable as the lag tends to zero.

At a strictly positive selected source time the heat lag is actually
unnecessary for spatial regularity.

The key observation is:

* the raw product convolution is an `L² × L²` Hilbert pairing, hence uniformly
  bounded in the output frequency;
* the positive-time moment induction gives arbitrarily high weighted `L¹`
  moments of the selected state;
* therefore a weighted `L¹` moment of order `2m` for the convolution implies
  its order-`m` weighted `L²` membership via

      (|ξ|^m |F*G|)^2
        ≤ ‖F*G‖_∞ |ξ|^(2m) |F*G|.

The divergence multiplier costs one radial power, while the Leray coefficients
are uniformly bounded.  Consequently every selected positive-time nonlinear
forcing coordinate has every finite radial Fourier `L²` weight.

This removes the apparent spatial endpoint singularity completely.  What
remains after this file is to make the resulting high-weight forcing package
uniform/continuous in source time on a positive compact slab.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open Filter
open MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedForcingRadialL2
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Frequency-independent L∞ bound for the raw product convolution -/

/-- Reflected translation preserves the raw Fourier `L²` norm exactly. -/
private theorem norm_h3SpectralScalarRawFourierReflectedShiftL2_eq
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖
      =
    ‖h3SpectralScalarRawFourierL2 G‖ := by
  unfold h3SpectralScalarRawFourierReflectedShiftL2
  exact
    MeasureTheory.Lp.norm_compMeasurePreserving
      (h3SpectralScalarRawFourierL2 G)
      (h3FourierSubLeftContinuousMapFamily_measurePreserving ξ)

/--
The genuine raw product convolution is uniformly bounded in frequency by the
product of two fixed Fourier `L²` norms.
-/
private theorem norm_h3RawProductConvolution_le_rawL2Product
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3RawProductConvolution F G ξ‖
      ≤
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖ := by

  rw [h3RawProductConvolution_eq_inner_conjRaw_shift]

  calc
    ‖inner ℂ
        (h3SpectralScalarRawFourierConjL2 F)
        (h3SpectralScalarRawFourierReflectedShiftL2 G ξ)‖
        ≤
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierReflectedShiftL2 G ξ‖ :=
      norm_inner_le_norm _ _
    _ =
      ‖h3SpectralScalarRawFourierConjL2 F‖ *
        ‖h3SpectralScalarRawFourierL2 G‖ := by
      rw [norm_h3SpectralScalarRawFourierReflectedShiftL2_eq]

/-! ## Double L¹ moment -> half-order L² convolution weight -/

/--
If both raw input states have a `2m` weighted Fourier `L¹` moment, then their
raw product convolution has the order-`m` radial weight in Fourier `L²`.
-/
theorem h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * m : ℕ) : ℝ))
        G) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawProductConvolution F G ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  let B : ℝ :=
    ‖h3SpectralScalarRawFourierConjL2 F‖ *
      ‖h3SpectralScalarRawFourierL2 G‖

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity

  have hMomentGeneric :=
    h3RawProductConvolution_moment_integrable_of
      (q := (((2 * m : ℕ) : ℝ)))
      (by positivity)
      F G hF hG

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ (2 * m) *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [
      h3FourierMomentWeight_natCast
    ] using hMomentGeneric

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            h3RawProductConvolution F G ξ)
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow m)).aestronglyMeasurable.mul
        (h3RawProductConvolution_integrable F G).1

  rw [memLp_two_iff_integrable_sq_norm hMeas]

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          B *
            (‖ξ‖ ^ (2 * m) *
              ‖h3RawProductConvolution F G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul B

  have hSqMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖((‖ξ‖ ^ m : ℝ) : ℂ) *
              h3RawProductConvolution F G ξ‖ ^ 2)
        (volume : Measure H3FourierPoint3) :=
    (hMeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable

  refine hMajor.mono' hSqMeas ?_

  filter_upwards with ξ

  have hr0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 : 0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hConv0 :
      0 ≤ ‖h3RawProductConvolution F G ξ‖ :=
    norm_nonneg _

  have hBound :
      ‖h3RawProductConvolution F G ξ‖ ≤ B := by
    dsimp only [B]
    exact
      norm_h3RawProductConvolution_le_rawL2Product
        F G ξ

  have hPow :
      (‖ξ‖ ^ m) ^ 2
        =
      ‖ξ‖ ^ (2 * m) := by
    rw [pow_two, ← pow_add]
    congr 1
    omega

  have hSq :
      (‖ξ‖ ^ m *
          ‖h3RawProductConvolution F G ξ‖) ^ 2
        ≤
      B *
        (‖ξ‖ ^ (2 * m) *
          ‖h3RawProductConvolution F G ξ‖) := by
    rw [mul_pow, hPow]
    calc
      ‖ξ‖ ^ (2 * m) *
          ‖h3RawProductConvolution F G ξ‖ ^ 2
          =
        ‖ξ‖ ^ (2 * m) *
          (‖h3RawProductConvolution F G ξ‖ *
            ‖h3RawProductConvolution F G ξ‖) := by
          rw [pow_two]
      _ ≤
        ‖ξ‖ ^ (2 * m) *
          (B *
            ‖h3RawProductConvolution F G ξ‖) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                hBound hConv0)
              (pow_nonneg hr0 (2 * m))
      _ =
        B *
          (‖ξ‖ ^ (2 * m) *
            ‖h3RawProductConvolution F G ξ‖) := by
          ring

  change
    ‖(‖((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawProductConvolution F G ξ‖ ^ 2 : ℝ)‖
      ≤
    B *
      (‖ξ‖ ^ (2 * m) *
        ‖h3RawProductConvolution F G ξ‖)

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _),
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0
  ]

  exact hSq

/-! ## One divergence derivative shifts the radial order by one -/

/--
An order-`m+1` radial `L²` product convolution controls the order-`m`
radially weighted Fourier derivative-convolution.
-/
private theorem h3FourierDerivative_mul_rawProductConvolution_radialWeight_memLp2
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hConv :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
            h3RawProductConvolution F G ξ)
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          (h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  have hTwoPi : 0 ≤ 2 * Real.pi := by
    positivity

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ))
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow m)).aestronglyMeasurable.mul
        (h3FourierDerivative_mul_rawProductConvolution_integrable
          F G j).1

  have hMajor :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (((2 * Real.pi : ℝ) : ℂ) *
            (((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
              h3RawProductConvolution F G ξ)))
        2
        (volume : Measure H3FourierPoint3) :=
    hConv.const_mul (((2 * Real.pi : ℝ) : ℂ))

  refine hMajor.of_le hMeas ?_

  filter_upwards with ξ

  have hr0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 : 0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hrSucc0 : 0 ≤ ‖ξ‖ ^ (m + 1) :=
    pow_nonneg hr0 (m + 1)

  have hDeriv :
      ‖h3FourierDerivativeSymbol j ξ‖
        ≤
      (2 * Real.pi) * ‖ξ‖ := by
    calc
      ‖h3FourierDerivativeSymbol j ξ‖
          ≤
        h3FourierGradientMagnitude ξ :=
        norm_h3FourierDerivativeSymbol_le_gradientMagnitude
          j ξ
      _ =
        (2 * Real.pi) * ‖ξ‖ := by
        unfold h3FourierGradientMagnitude
        rfl

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrm0,
    norm_mul,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hTwoPi,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hrSucc0
  ]

  calc
    ‖ξ‖ ^ m *
        (‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ‖ξ‖ ^ m *
        (((2 * Real.pi) * ‖ξ‖) *
          ‖h3RawProductConvolution F G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hDeriv
            (norm_nonneg _))
          hrm0
    _ =
      (2 * Real.pi) *
        (‖ξ‖ ^ (m + 1) *
          ‖h3RawProductConvolution F G ξ‖) := by
      rw [pow_succ]
      ring

/-! ## Finite divergence and Leray projection preserve radial L² -/

/--
If every scalar input coordinate has the required doubled moment, the finite
outer-product divergence has order-`m` radial Fourier `L²`.
-/
private theorem h3RawFinOuterProductDivergence_radialWeight_memLp2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U k))
    (hV :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V k)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinOuterProductDivergence U V i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hTerm :
      ∀ j : Fin 3,
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
              (h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ))
          2
          (volume : Measure H3FourierPoint3) := by
    intro j

    have hConv :
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
              h3RawProductConvolution (U i) (V j) ξ)
          2
          (volume : Measure H3FourierPoint3) :=
      h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
        (m + 1)
        (U i)
        (V j)
        (by
          simpa only [
            Nat.mul_add,
            Nat.mul_one
          ] using hU i)
        (by
          simpa only [
            Nat.mul_add,
            Nat.mul_one
          ] using hV j)

    exact
      h3FourierDerivative_mul_rawProductConvolution_radialWeight_memLp2
        m (U i) (V j) j hConv

  have hSum :=
    MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j _ => hTerm j)

  unfold h3RawFinOuterProductDivergence

  simpa only [
    Finset.mul_sum
  ] using hSum

/--
A bounded Leray coefficient preserves an arbitrary radial Fourier `L²` weight.
-/
private theorem h3LerayCoefficient_mul_rawFinOuterProductDivergence_radialWeight_memLp2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hDiv :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            h3RawFinOuterProductDivergence U V k ξ)
        2
        (volume : Measure H3FourierPoint3)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          (h3LerayCoefficient ξ i k *
            h3RawFinOuterProductDivergence U V k ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            (h3LerayCoefficient ξ i k *
              h3RawFinOuterProductDivergence U V k ξ))
        (volume : Measure H3FourierPoint3) := by
    exact
      (Complex.continuous_ofReal.comp
        (continuous_norm.pow m)).aestronglyMeasurable.mul
        (h3LerayCoefficient_mul_rawFinOuterProductDivergence_integrable
          U V i k).1

  have hMajor :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (2 : ℂ) *
            (((‖ξ‖ ^ m : ℝ) : ℂ) *
              h3RawFinOuterProductDivergence U V k ξ))
        2
        (volume : Measure H3FourierPoint3) :=
    hDiv.const_mul (2 : ℂ)

  refine hMajor.of_le hMeas ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul, norm_mul]

  have hCoeff :
      ‖h3LerayCoefficient ξ i k‖ ≤ 2 :=
    norm_h3LerayCoefficient_le_two ξ i k

  have hDivNonneg :
      0 ≤ ‖h3RawFinOuterProductDivergence U V k ξ‖ :=
    norm_nonneg _

  norm_num

  calc
    ‖ξ‖ ^ m *
        (‖h3LerayCoefficient ξ i k‖ *
          ‖h3RawFinOuterProductDivergence U V k ξ‖)
        ≤
      ‖ξ‖ ^ m *
        (2 *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          hCoeff
          hDivNonneg)
        (pow_nonneg (norm_nonneg ξ) m)
    _ =
      2 *
        (‖ξ‖ ^ m *
          ‖h3RawFinOuterProductDivergence U V k ξ‖) := by
      ring

/--
The complete finite Leray-projected nonlinear forcing inherits arbitrary radial
Fourier `L²` weight from sufficiently high raw input moments.
-/
theorem h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U k))
    (hV :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V k)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U V i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  have hDiv :
      ∀ k : Fin 3,
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
              h3RawFinOuterProductDivergence U V k ξ)
          2
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3RawFinOuterProductDivergence_radialWeight_memLp2
        m U V k hU hV

  have hTerm :
      ∀ k : Fin 3,
        MemLp
          (fun ξ : H3FourierPoint3 =>
            ((‖ξ‖ ^ m : ℝ) : ℂ) *
              (h3LerayCoefficient ξ i k *
                h3RawFinOuterProductDivergence U V k ξ))
          2
          (volume : Measure H3FourierPoint3) := by
    intro k
    exact
      h3LerayCoefficient_mul_rawFinOuterProductDivergence_radialWeight_memLp2
        m U V i k (hDiv k)

  have hSum :=
    MeasureTheory.memLp_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hTerm k)

  unfold h3RawFinLerayOuterProductDivergence

  simpa only [
    Finset.mul_sum
  ] using hSum

/-! ## Selected positive-time forcing has every finite radial L² weight -/

/--
At every positive selected restart time, every finite radial weight of the
unheated nonlinear forcing belongs to Fourier `L²`.
-/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_radialWeight_memLp2
    {ν A s : ℝ}
    (m : ℕ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hMoment :
      ∀ k : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (W s k) := by
    intro k
    unfold H3RawFourierMomentIntegrable
    dsimp only [W]

    have hNat :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_natMoment_integrable
        (2 * (m + 1))
        hν U₀ hA hU₀ hs hsR k

    simpa only [
      h3FourierMomentWeight_natCast
    ] using hNat

  exact
    h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
      m (W s) (W s) i hMoment hMoment

/-!
In particular, the fourth and fifth weighted unheated forcing slices required
by the terminal Duhamel frontier are automatic at every strict source time.
The remaining work is now temporal control of these high-weight forcing states
on a compact positive source-time slab.
-/

end

end Euclidean
end Bridge
end PrimeTensor
