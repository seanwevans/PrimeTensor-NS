import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Longitudinal.Equatorial.Vorticity.Physical.Dissipation.Top.Radial.Tail.Temporal.Forward.PDE.TopDissipation.Forcing.Product.Bound

/-!
# Quantitative radial L² bound for the finite Leray forcing

The scalar checkpoint gives a quantitative `L²` estimate for

    |ξ|^(m+1) (F * G).

This file transports that estimate through the finite Navier--Stokes
nonlinearity:

1. one divergence derivative costs at most `2π`;
2. the finite divergence is a sum over three coordinates;
3. one Leray coefficient costs at most `2`;
4. the complete projected forcing is another sum over three coordinates.

We deliberately retain the finite sums instead of collapsing them into a
large opaque constant.  The resulting bound is

    ‖ |ξ|^m P div(U ⊗ V)_i ‖₂
      ≤
    ∑ k, 2 * ∑ j, (2π) *
      ‖ |ξ|^(m+1) (Û_k * V̂_j) ‖₂.

Each scalar convolution norm on the right is controlled by the quantitative
Young estimate from `Product/Bound`.

This is precisely the finite-dimensional bilinear estimate needed to turn
strong arbitrary-radial convergence of the selected velocity difference
quotient into convergence of the nonlinear forcing quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RadialForcingBilinearBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

set_option maxHeartbeats 2600000

/-! ## One derivative-convolution term -/

/--
One order-`m` radially weighted derivative-convolution belongs to Fourier
`L²`, using doubled moment order `2(m+1)` on both inputs.
-/
theorem h3FourierDerivativeRawProductConvolution_radialWeight_memLp2
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        G) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          (h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution F G ξ))
      2
      (volume : Measure H3FourierPoint3) := by

  have hConv :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
            h3RawProductConvolution F G ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    h3RawProductConvolution_radialWeight_memLp2_of_doubleMoment
      (m + 1) F G hF hG

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution F G ξ))
        (volume : Measure H3FourierPoint3) :=
    (Complex.continuous_ofReal.comp
      (continuous_norm.pow m)).aestronglyMeasurable.mul
      (h3FourierDerivative_mul_rawProductConvolution_integrable
        F G j).1

  have hMajor :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (((2 * Real.pi : ℝ) : ℂ) *
            (
              ((‖ξ‖ ^ (m + 1) : ℝ) : ℂ) *
                h3RawProductConvolution F G ξ
            )))
        2
        (volume : Measure H3FourierPoint3) :=
    hConv.const_mul (((2 * Real.pi : ℝ) : ℂ))

  refine hMajor.of_le hMeas ?_

  filter_upwards with ξ

  have hr0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 :
      0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hrSucc0 :
      0 ≤ ‖ξ‖ ^ (m + 1) :=
    pow_nonneg hr0 (m + 1)

  have hTwoPi :
      0 ≤ 2 * Real.pi := by
    positivity

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

/--
Canonical Fourier `L²` package of one radial derivative-convolution term.
-/
noncomputable def h3FourierDerivativeRawProductConvolutionRadialFourierL2
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        G) :
    H3FourierComplexL2 :=
  (
    h3FourierDerivativeRawProductConvolution_radialWeight_memLp2
      m F G j hF hG
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ))

theorem h3FourierDerivativeRawProductConvolutionRadialFourierL2_ae
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        G) :
    (
      (
        h3FourierDerivativeRawProductConvolutionRadialFourierL2
          m F G j hF hG :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        (h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ)) := by

  unfold
    h3FourierDerivativeRawProductConvolutionRadialFourierL2

  exact
    MemLp.coeFn_toLp
      (
        h3FourierDerivativeRawProductConvolution_radialWeight_memLp2
          m F G j hF hG
      )

/--
One derivative symbol costs at most `2π` relative to the next radial
convolution level.
-/
theorem norm_h3FourierDerivativeRawProductConvolutionRadialFourierL2_le
    (m : ℕ)
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (hF :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        F)
    (hG :
      H3RawFourierMomentIntegrable
        (((2 * (m + 1) : ℕ) : ℝ))
        G) :
    ‖h3FourierDerivativeRawProductConvolutionRadialFourierL2
        m F G j hF hG‖
      ≤
    (2 * Real.pi) *
      ‖h3RawProductConvolutionRadialFourierL2
          (m + 1) F G hF hG‖ := by

  apply
    Lp.norm_le_mul_norm_of_ae_le_mul

  have hD :=
    h3FourierDerivativeRawProductConvolutionRadialFourierL2_ae
      m F G j hF hG

  have hC :=
    h3RawProductConvolutionRadialFourierL2_ae
      (m + 1) F G hF hG

  filter_upwards [hD, hC]
    with ξ hDξ hCξ

  rw [hDξ, hCξ]

  have hr0 :
      0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  have hrm0 :
      0 ≤ ‖ξ‖ ^ m :=
    pow_nonneg hr0 m

  have hrSucc0 :
      0 ≤ ‖ξ‖ ^ (m + 1) :=
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
        (
          ‖ξ‖ ^ (m + 1) *
            ‖h3RawProductConvolution F G ξ‖
        ) := by
      rw [pow_succ]
      ring

/-! ## Finite divergence package -/

/--
Order-`m` radial Fourier `L²` package of one finite pre-Leray divergence
coordinate.
-/
noncomputable def h3RawFinOuterProductDivergenceRadialFourierL2
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
    H3FourierComplexL2 :=
  ∑ j : Fin 3,
    h3FourierDerivativeRawProductConvolutionRadialFourierL2
      m (U i) (V j) j (hU i) (hV j)

/--
The finite divergence package has exactly the radial raw divergence
representative.
-/
theorem h3RawFinOuterProductDivergenceRadialFourierL2_ae
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
    (
      (
        h3RawFinOuterProductDivergenceRadialFourierL2
          m U V i hU hV :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinOuterProductDivergence U V i ξ) := by

  unfold
    h3RawFinOuterProductDivergenceRadialFourierL2

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun j : Fin 3 =>
        h3FourierDerivativeRawProductConvolutionRadialFourierL2
          m (U i) (V j) j (hU i) (hV j))

  have hTerms :
      ∀ᵐ ξ : H3FourierPoint3
        ∂(volume : Measure H3FourierPoint3),
        ∀ j : Fin 3,
          (
            (
              h3FourierDerivativeRawProductConvolutionRadialFourierL2
                m (U i) (V j) j (hU i) (hV j) :
              H3FourierComplexL2
            ) :
            H3FourierPoint3 → ℂ
          ) ξ
            =
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            (
              h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ
            ) := by

    exact
      ae_all_iff.2
        (fun j =>
          h3FourierDerivativeRawProductConvolutionRadialFourierL2_ae
            m (U i) (V j) j (hU i) (hV j))

  filter_upwards [hSum, hTerms]
    with ξ hSumξ hTermsξ

  rw [hSumξ]
  simp only [Finset.sum_apply]

  unfold h3RawFinOuterProductDivergence

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro j hj

  exact hTermsξ j

/--
Finite divergence norm bound by the three scalar radial convolution norms one
order higher.
-/
theorem norm_h3RawFinOuterProductDivergenceRadialFourierL2_le
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
    ‖h3RawFinOuterProductDivergenceRadialFourierL2
        m U V i hU hV‖
      ≤
    ∑ j : Fin 3,
      (2 * Real.pi) *
        ‖h3RawProductConvolutionRadialFourierL2
            (m + 1)
            (U i) (V j)
            (hU i) (hV j)‖ := by

  calc
    ‖h3RawFinOuterProductDivergenceRadialFourierL2
        m U V i hU hV‖
        ≤
      ∑ j : Fin 3,
        ‖h3FourierDerivativeRawProductConvolutionRadialFourierL2
            m (U i) (V j) j
            (hU i) (hV j)‖ := by
      unfold
        h3RawFinOuterProductDivergenceRadialFourierL2
      exact
        norm_sum_le
          (Finset.univ : Finset (Fin 3))
          (fun j : Fin 3 =>
            h3FourierDerivativeRawProductConvolutionRadialFourierL2
              m (U i) (V j) j
              (hU i) (hV j))
    _ ≤
      ∑ j : Fin 3,
        (2 * Real.pi) *
          ‖h3RawProductConvolutionRadialFourierL2
              (m + 1)
              (U i) (V j)
              (hU i) (hV j)‖ := by
      exact
        Finset.sum_le_sum
          (fun j _ =>
            norm_h3FourierDerivativeRawProductConvolutionRadialFourierL2_le
              m (U i) (V j) j
              (hU i) (hV j))

/-! ## One Leray row term -/

/--
Multiplying the radial divergence package by one bounded Leray coefficient
preserves Fourier `L²`.
-/
theorem h3LerayCoefficient_mul_rawFinOuterProductDivergenceRadial_memLp2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3LerayCoefficient ξ i k *
          (
            h3RawFinOuterProductDivergenceRadialFourierL2
              m U V k hU hV
          ) ξ)
      2
      (volume : Measure H3FourierPoint3) := by

  let D : H3FourierComplexL2 :=
    h3RawFinOuterProductDivergenceRadialFourierL2
      m U V k hU hV

  have hMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3LerayCoefficient ξ i k * D ξ)
        (volume : Measure H3FourierPoint3) :=
    (measurable_h3LerayCoefficient i k).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable D)

  have hMajor :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          (2 : ℂ) * D ξ)
        2
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.Lp.memLp D).const_mul (2 : ℂ)

  refine hMajor.of_le hMeas ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul]

  have hCoeff :
      ‖h3LerayCoefficient ξ i k‖ ≤ 2 :=
    norm_h3LerayCoefficient_le_two ξ i k

  norm_num at hCoeff ⊢

  exact
    mul_le_mul_of_nonneg_right
      hCoeff
      (norm_nonneg (D ξ))

/--
Canonical Fourier `L²` package of one Leray row term.
-/
noncomputable def h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    H3FourierComplexL2 :=
  (
    h3LerayCoefficient_mul_rawFinOuterProductDivergenceRadial_memLp2
      m U V i k hU hV
  ).toLp
    (fun ξ : H3FourierPoint3 =>
      h3LerayCoefficient ξ i k *
        (
          h3RawFinOuterProductDivergenceRadialFourierL2
            m U V k hU hV
        ) ξ)

theorem h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2_ae
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    (
      (
        h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
          m U V i k hU hV :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3LerayCoefficient ξ i k *
        (
          h3RawFinOuterProductDivergenceRadialFourierL2
            m U V k hU hV
        ) ξ) := by

  unfold
    h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2

  exact
    MemLp.coeFn_toLp
      (
        h3LerayCoefficient_mul_rawFinOuterProductDivergenceRadial_memLp2
          m U V i k hU hV
      )

/--
One Leray coefficient costs at most the factor `2`.
-/
theorem norm_h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2_le
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i k : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    ‖h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
        m U V i k hU hV‖
      ≤
    2 *
      ‖h3RawFinOuterProductDivergenceRadialFourierL2
          m U V k hU hV‖ := by

  apply
    Lp.norm_le_mul_norm_of_ae_le_mul

  have hTerm :=
    h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2_ae
      m U V i k hU hV

  filter_upwards [hTerm]
    with ξ hTermξ

  rw [hTermξ, norm_mul]

  exact
    mul_le_mul_of_nonneg_right
      (norm_h3LerayCoefficient_le_two ξ i k)
      (norm_nonneg _)

/-! ## Complete radial Leray forcing package -/

/--
Canonical order-`m` radial Fourier `L²` package of one complete finite
Leray-divergence forcing coordinate.
-/
noncomputable def h3RawFinLerayOuterProductDivergenceRadialFourierL2
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    H3FourierComplexL2 :=
  ∑ k : Fin 3,
    h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
      m U V i k hU hV

/--
The complete package has the literal radial raw Leray forcing representative.
-/
theorem h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    (
      (
        h3RawFinLerayOuterProductDivergenceRadialFourierL2
          m U V i hU hV :
        H3FourierComplexL2
      ) :
      H3FourierPoint3 → ℂ
    )
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ((‖ξ‖ ^ m : ℝ) : ℂ) *
        h3RawFinLerayOuterProductDivergence
          U V i ξ) := by

  unfold
    h3RawFinLerayOuterProductDivergenceRadialFourierL2

  have hSum :=
    MeasureTheory.Lp.coeFn_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k : Fin 3 =>
        h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
          m U V i k hU hV)

  have hTerms :
      ∀ᵐ ξ : H3FourierPoint3
        ∂(volume : Measure H3FourierPoint3),
        ∀ k : Fin 3,
          (
            (
              h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
                m U V i k hU hV :
              H3FourierComplexL2
            ) :
            H3FourierPoint3 → ℂ
          ) ξ
            =
          h3LerayCoefficient ξ i k *
            (
              h3RawFinOuterProductDivergenceRadialFourierL2
                m U V k hU hV
            ) ξ := by

    exact
      ae_all_iff.2
        (fun k =>
          h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2_ae
            m U V i k hU hV)

  have hDiv :
      ∀ᵐ ξ : H3FourierPoint3
        ∂(volume : Measure H3FourierPoint3),
        ∀ k : Fin 3,
          (
            (
              h3RawFinOuterProductDivergenceRadialFourierL2
                m U V k hU hV :
              H3FourierComplexL2
            ) :
            H3FourierPoint3 → ℂ
          ) ξ
            =
          ((‖ξ‖ ^ m : ℝ) : ℂ) *
            h3RawFinOuterProductDivergence U V k ξ := by

    exact
      ae_all_iff.2
        (fun k =>
          h3RawFinOuterProductDivergenceRadialFourierL2_ae
            m U V k hU hV)

  filter_upwards [hSum, hTerms, hDiv]
    with ξ hSumξ hTermsξ hDivξ

  rw [hSumξ]
  simp only [Finset.sum_apply]

  unfold h3RawFinLerayOuterProductDivergence

  rw [Finset.mul_sum]

  apply Finset.sum_congr rfl
  intro k hk

  rw [hTermsξ k, hDivξ k]

  ring

/--
Quantitative finite-dimensional radial forcing bound.
-/
theorem norm_h3RawFinLerayOuterProductDivergenceRadialFourierL2_le
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    ‖h3RawFinLerayOuterProductDivergenceRadialFourierL2
        m U V i hU hV‖
      ≤
    ∑ k : Fin 3,
      2 *
        (
          ∑ j : Fin 3,
            (2 * Real.pi) *
              ‖h3RawProductConvolutionRadialFourierL2
                  (m + 1)
                  (U k) (V j)
                  (hU k) (hV j)‖
        ) := by

  calc
    ‖h3RawFinLerayOuterProductDivergenceRadialFourierL2
        m U V i hU hV‖
        ≤
      ∑ k : Fin 3,
        ‖h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
            m U V i k hU hV‖ := by
      unfold
        h3RawFinLerayOuterProductDivergenceRadialFourierL2
      exact
        norm_sum_le
          (Finset.univ : Finset (Fin 3))
          (fun k : Fin 3 =>
            h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2
              m U V i k hU hV)
    _ ≤
      ∑ k : Fin 3,
        2 *
          ‖h3RawFinOuterProductDivergenceRadialFourierL2
              m U V k hU hV‖ := by
      exact
        Finset.sum_le_sum
          (fun k _ =>
            norm_h3LerayCoefficientRawFinOuterProductDivergenceRadialFourierL2_le
              m U V i k hU hV)
    _ ≤
      ∑ k : Fin 3,
        2 *
          (
            ∑ j : Fin 3,
              (2 * Real.pi) *
                ‖h3RawProductConvolutionRadialFourierL2
                    (m + 1)
                    (U k) (V j)
                    (hU k) (hV j)‖
          ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact
        mul_le_mul_of_nonneg_left
          (
            norm_h3RawFinOuterProductDivergenceRadialFourierL2_le
              m U V k hU hV
          )
          (by norm_num)

/--
The canonical package agrees with the direct `MemLp.toLp` package used by the
selected forcing product-rule layer.
-/
theorem h3RawFinLerayOuterProductDivergenceRadialFourierL2_eq_toLp
    (m : ℕ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (hU :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (U r))
    (hV :
      ∀ r : Fin 3,
        H3RawFourierMomentIntegrable
          (((2 * (m + 1) : ℕ) : ℝ))
          (V r)) :
    h3RawFinLerayOuterProductDivergenceRadialFourierL2
        m U V i hU hV
      =
    (
      h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
        m U V i hU hV
    ).toLp
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ m : ℝ) : ℂ) *
          h3RawFinLerayOuterProductDivergence U V i ξ) := by

  apply MeasureTheory.Lp.ext

  have hLeft :=
    h3RawFinLerayOuterProductDivergenceRadialFourierL2_ae
      m U V i hU hV

  have hRight :=
    MemLp.coeFn_toLp
      (
        h3RawFinLerayOuterProductDivergence_radialWeight_memLp2
          m U V i hU hV
      )

  filter_upwards [hLeft, hRight]
    with ξ hLeftξ hRightξ

  rw [hLeftξ, hRightξ]

end

end Euclidean
end Bridge
end PrimeTensor
