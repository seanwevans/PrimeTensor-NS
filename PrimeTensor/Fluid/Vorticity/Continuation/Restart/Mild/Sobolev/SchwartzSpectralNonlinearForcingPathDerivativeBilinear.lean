import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.SchwartzSpectralNonlinearForcingPathDerivativeTimeIntegrability
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.WeightedConvolutionBilinear

/-!
# Bilinear decomposition of the pointwise nonlinear derivative path

The time-integrability module leaves continuity of the retarded pointwise
first-derivative representative as the remaining local analytic obligation.
The existing H³ retarded-kernel continuity proof handles the same problem by
splitting a difference into two input-variation terms and one frozen-input
time-variation term.

This file installs the corresponding exact algebra for the classical
inverse-Fourier derivative representative.  The raw convolution is already
bilinear, so we lift subtraction through finite divergence, the finite Leray
sum, the heat multiplier, and finally the ordinary inverse Fourier integral.
At positive lag we obtain

    Rτ(U-U₀,V) = Rτ(U,V) - Rτ(U₀,V),
    Rτ(U,V-V₀) = Rτ(U,V) - Rτ(U,V₀).

Consequently a retarded path difference admits the exact three-term split
needed by the next continuity estimate.  No new analytic estimate is used in
this module.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter FourierTransform
open scoped BigOperators ENNReal NNReal Topology Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralNonlinearForcingPathDerivativeBilinear
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Raw finite forcing subtraction -/

/-- Raw finite outer-product divergence is subtractive in its first vector
input. -/
theorem h3RawFinOuterProductDivergence_sub_left
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence (U - V) W i ξ
      =
    h3RawFinOuterProductDivergence U W i ξ -
      h3RawFinOuterProductDivergence V W i ξ := by
  unfold h3RawFinOuterProductDivergence
  simp_rw [Pi.sub_apply, h3RawProductConvolution_sub_left, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Raw finite outer-product divergence is subtractive in its second vector
input. -/
theorem h3RawFinOuterProductDivergence_sub_right
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinOuterProductDivergence U (V - W) i ξ
      =
    h3RawFinOuterProductDivergence U V i ξ -
      h3RawFinOuterProductDivergence U W i ξ := by
  unfold h3RawFinOuterProductDivergence
  simp_rw [Pi.sub_apply, h3RawProductConvolution_sub_right, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The complete raw finite Leray-divergence forcing is subtractive in its
first vector input. -/
theorem h3RawFinLerayOuterProductDivergence_sub_left
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence (U - V) W i ξ
      =
    h3RawFinLerayOuterProductDivergence U W i ξ -
      h3RawFinLerayOuterProductDivergence V W i ξ := by
  unfold h3RawFinLerayOuterProductDivergence
  simp_rw [h3RawFinOuterProductDivergence_sub_left, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The complete raw finite Leray-divergence forcing is subtractive in its
second vector input. -/
theorem h3RawFinLerayOuterProductDivergence_sub_right
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergence U (V - W) i ξ
      =
    h3RawFinLerayOuterProductDivergence U V i ξ -
      h3RawFinLerayOuterProductDivergence U W i ξ := by
  unfold h3RawFinLerayOuterProductDivergence
  simp_rw [h3RawFinOuterProductDivergence_sub_right, mul_sub]
  rw [Finset.sum_sub_distrib]

/-! ## Positive-lag heat amplitude subtraction -/

/-- Positive-lag raw heat forcing is subtractive in its first input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_left
    (ν τ : ℝ)
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ (U - V) W i ξ
      =
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U W i ξ
      -
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ V W i ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [h3RawFinLerayOuterProductDivergence_sub_left]
  ring

/-- Positive-lag raw heat forcing is subtractive in its second input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_right
    (ν τ : ℝ)
    (U V W : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U (V - W) i ξ
      =
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U V i ξ
      -
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν τ U W i ξ := by
  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [h3RawFinLerayOuterProductDivergence_sub_right]
  ring

/-! ## Classical derivative-representative subtraction -/

/-- At positive lag, the classical first-derivative representative is
subtractive in its first spectral input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_left
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V W : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ (U - V) W i j x
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U W i j x
      -
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ V W i j x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]
  rw [Real.fourier_eq]
  rw [Real.fourier_eq]

  have hUInt :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ U W i j
  have hVInt :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ V W i j

  have hUKernel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 (-(inner ℝ ξ (-x))) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U W i ξ))
        volume := by
    rw [Real.fourierIntegral_convergent_iff (-x)]
    exact hUInt

  have hVKernel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 (-(inner ℝ ξ (-x))) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ V W i ξ))
        volume := by
    rw [Real.fourierIntegral_convergent_iff (-x)]
    exact hVInt

  rw [← integral_sub hUKernel hVKernel]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_left]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- At positive lag, the classical first-derivative representative is
subtractive in its second spectral input. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_right
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V W : H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U (V - W) i j x
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U V i j x
      -
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ U W i j x := by
  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Real.fourier_eq]
  rw [Real.fourier_eq]
  rw [Real.fourier_eq]

  have hVInt :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ U V i j
  have hWInt :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
      hν hτ U W i j

  have hVKernel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 (-(inner ℝ ξ (-x))) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ))
        volume := by
    rw [Real.fourierIntegral_convergent_iff (-x)]
    exact hVInt

  have hWKernel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          𝐞 (-(inner ℝ ξ (-x))) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U W i ξ))
        volume := by
    rw [Real.fourierIntegral_convergent_iff (-x)]
    exact hWInt

  rw [← integral_sub hVKernel hWKernel]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [h3RawFinLerayOuterProductDivergenceHeatRepresentative_sub_right]
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-! ## Retarded three-term difference decomposition -/

/-- Exact decomposition of a retarded derivative-path difference into two
input-variation terms and one frozen-input time-variation term.  This is the
pointwise analogue of the decomposition used for the H³ heat--Leray path. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_sub_decomposition
    {ν t s s₀ : ℝ}
    (hν : 0 < ν)
    (hs : s < t)
    (hs₀ : s₀ < t)
    (U V : ℝ → H3SpectralFinVectorState)
    (i j : Fin 3)
    (x : H3FourierPoint3) :
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x s
      -
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        ν t U V i j x s₀
      =
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s) (U s - U s₀) (V s) i j x
      +
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s) (U s₀) (V s - V s₀) i j x
      +
    (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s) (U s₀) (V s₀) i j x
      -
     h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν (t - s₀) (U s₀) (V s₀) i j x) := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  have _hτ₀ : 0 < t - s₀ := sub_pos.mpr hs₀

  unfold h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath

  have hA :=
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_left
      hν hτ (U s) (U s₀) (V s) i j x

  have hB :=
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_sub_right
      hν hτ (U s₀) (V s) (V s₀) i j x

  rw [hA, hB]
  abel

end

end Euclidean
end Bridge
end PrimeTensor
