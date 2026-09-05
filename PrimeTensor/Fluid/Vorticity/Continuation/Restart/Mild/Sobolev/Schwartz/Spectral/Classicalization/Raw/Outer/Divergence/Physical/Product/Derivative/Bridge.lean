import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative

/-!
# Classicalization: raw outer divergence as physical product derivatives

The unprojected nonlinear Fourier term is

    div(U ⊗ V)_i
      = ∑ j d_j (rawConv(U_i,V_j)).

Before comparing the Leray-projected forcing with physical advection, we first
transport this raw divergence through the ordinary inverse Fourier transform.

There are two bookkeeping steps.

* inverse Fourier commutes with the finite coordinate sum because every
  differentiated raw product convolution is integrable;
* the raw Fourier field of the bundled weighted H³ product convolution agrees
  almost everywhere with the exact raw convolution, so the already-proved
  Point3 derivative formula identifies each inverse-Fourier derivative
  multiplier with the spatial derivative of the canonical real C¹ product
  representative.

Thus the real part of the inverse Fourier transform of the complete raw finite
outer-product divergence is exactly the finite sum of physical coordinate
derivatives of the canonical H³ product representatives.

No new estimate, product theorem, Leray identity, or incompressibility argument
is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3RawOuterDivergencePhysicalProductDerivativeBridge
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Ordinary inverse Fourier transform commutes with the finite sum defining
one raw outer-product divergence coordinate. -/
theorem h3RawFinOuterProductDivergence_fourierInv_eq_sum_coordinateDerivatives
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence U V i)
        x
      =
    ∑ j : Fin 3,
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol j ξ *
            h3RawProductConvolution (U i) (V j) ξ)
        x := by
  have hPhaseIntegrable :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            𝐞 (inner ℝ ξ x) •
              (h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ))
          (volume : Measure H3FourierPoint3) := by
    intro j

    have h :
        Integrable
          (fun ξ : H3FourierPoint3 =>
            𝐞 (-(inner ℝ ξ (-x))) •
              (h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (U i) (V j) ξ))
          (volume : Measure H3FourierPoint3) := by
      rw [Real.fourierIntegral_convergent_iff (-x)]
      exact
        h3FourierDerivative_mul_rawProductConvolution_integrable
          (U i) (V j) j

    simpa only [inner_neg_right, neg_neg] using h

  have hIntegralSum :
      (∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3,
          𝐞 (inner ℝ ξ x) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution (U i) (V j) ξ))
        =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          𝐞 (inner ℝ ξ x) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution (U i) (V j) ξ) := by
    simpa using
      (MeasureTheory.integral_finsetSum
        (μ := (volume : Measure H3FourierPoint3))
        Finset.univ
        (fun j _ => hPhaseIntegrable j))

  simp_rw [Real.fourierInv_eq]

  calc
    (∫ ξ : H3FourierPoint3,
      𝐞 (inner ℝ ξ x) •
        h3RawFinOuterProductDivergence U V i ξ)
        =
      ∫ ξ : H3FourierPoint3,
        ∑ j : Fin 3,
          𝐞 (inner ℝ ξ x) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution (U i) (V j) ξ) := by
          apply integral_congr_ae
          filter_upwards with ξ

          unfold h3RawFinOuterProductDivergence
          rw [Finset.smul_sum]
    _ =
      ∑ j : Fin 3,
        ∫ ξ : H3FourierPoint3,
          𝐞 (inner ℝ ξ x) •
            (h3FourierDerivativeSymbol j ξ *
              h3RawProductConvolution (U i) (V j) ξ) :=
      hIntegralSum

/-- One differentiated raw product convolution reconstructs as the physical
coordinate derivative of the canonical real C¹ representative of the bundled
weighted H³ product state. -/
theorem h3WeightedRawProductConvolutionL2_spatialDerivative_fin_eq_rawProductConvolutionDerivativeFourierInv_re
    (F G : H3SpectralScalarState)
    (j : Fin 3)
    (x : Point3) :
    spatial3.d
        (h3AxisOfFin3 j)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3WeightedRawProductConvolutionL2 F G))
        x
      =
    (FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  let H : H3SpectralScalarState :=
    h3WeightedRawProductConvolutionL2 F G

  have hRaw :
      h3SpectralScalarRawFourier H
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3RawProductConvolution F G := by
    dsimp only [H]
    exact
      h3SpectralScalarRawFourier_weightedRawProductConvolutionL2_ae
        F G

  have hDerivativeAE :
      h3SpectralScalarRawFourierCoordinateDerivative H j
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol j ξ *
          h3RawProductConvolution F G ξ) := by
    filter_upwards [hRaw] with ξ hξ
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    rw [hξ]

  rw [
    h3SpectralScalarRealC1RepresentativeOnPoint3_spatialDerivative_fin
  ]

  apply congrArg Complex.re

  rw [
    Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg
  ]

  exact
    Real.fourier_congr_ae
      hDerivativeAE
      (-((WithLp.toLp 2 : Point3 → H3FourierPoint3) x))

/-- The real physical representative of the complete raw finite outer-product
divergence is the sum of coordinate derivatives of the canonical H³ product
representatives. -/
theorem h3RawFinOuterProductDivergence_fourierInv_re_eq_sum_productRepresentative_spatialDerivatives
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : Point3) :
    (FourierTransformInv.fourierInv
      (h3RawFinOuterProductDivergence U V i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re
      =
    ∑ j : Fin 3,
      spatial3.d
        (h3AxisOfFin3 j)
        (h3SpectralScalarRealC1RepresentativeOnPoint3
          (h3WeightedRawProductConvolutionL2
            (U i) (V j)))
        x := by
  rw [
    h3RawFinOuterProductDivergence_fourierInv_eq_sum_coordinateDerivatives
  ]

  simp only [
    Fin.sum_univ_three,
    Complex.add_re
  ]

  rw [
    ←
      h3WeightedRawProductConvolutionL2_spatialDerivative_fin_eq_rawProductConvolutionDerivativeFourierInv_re
        (U i) (V 0) 0 x,
    ←
      h3WeightedRawProductConvolutionL2_spatialDerivative_fin_eq_rawProductConvolutionDerivativeFourierInv_re
        (U i) (V 1) 1 x,
    ←
      h3WeightedRawProductConvolutionL2_spatialDerivative_fin_eq_rawProductConvolutionDerivativeFourierInv_re
        (U i) (V 2) 2 x
  ]

end

end Euclidean
end Bridge
end PrimeTensor
