import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Second.Convolution.Majorant.Mass

/-!
# Quantitative second-moment mass bound for the exact raw convolution

`SecondConvolutionMajorantMass` computes the exact total mass of the Young
majorant already used by `SelectedConvolutionSecond`.

This file exposes the pointwise domination that was local to the qualitative
integrability proof,

    |ξ|² |(F̂ * Ĝ)(ξ)|
      ≤
    M₂(F,G)(ξ)

for almost every frequency, and integrates it.

The result is the numerical convolution estimate

    m₂(F * G)
      ≤
    2 (m₂(F)m₀(G) + m₀(F)m₂(G)).

This is the scalar estimate needed before spending one Fourier power on the
divergence derivative in the first forcing moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSecondConvolutionMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual second raw Fourier `L¹` mass of the exact product convolution. -/
noncomputable def h3RawProductConvolutionSecondMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ ^ 2 *
      ‖h3RawProductConvolution F G ξ‖

/-- The exact raw convolution is dominated almost everywhere by the same
second-moment Young majorant used in the qualitative integrability proof. -/
theorem h3RawProductConvolution_secondMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      ‖ξ‖ ^ 2 *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionSecondMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let f2 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 2 *
        ‖h3SpectralScalarRawFourier F η‖

  let g2 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 2 *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable f0 (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hG0 :
      Integrable g0 (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hLeftProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f2 p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF2.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      f2, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * g2 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG2
    simpa only [
      f0, g2,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f2 η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * g2 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw : 0 ≤ ‖ξ‖ ^ 2 :=
    pow_nonneg (norm_nonneg ξ) 2

  have hRawKernel :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η))
        (volume : Measure H3FourierPoint3) :=
    h3RawProductKernel_integrable F G ξ

  have hRawWeighted :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul (‖ξ‖ ^ 2)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          2 *
            (f2 η * g0 (ξ - η) +
              f0 η * g2 (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul 2

  have hPointwise :
      ∀ η : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        2 *
          (f2 η * g0 (ξ - η) +
            f0 η * g2 (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierNorm_sq_le_two_sq_add_sq ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        ‖ξ‖ ^ 2 *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
              rw [norm_mul]
      _ ≤
        (2 * (‖η‖ ^ 2 + ‖ξ - η‖ ^ 2)) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        2 *
          (f2 η * g0 (ξ - η) +
            f0 η * g2 (ξ - η)) := by
        dsimp only [f0, g0, f2, g2]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        2 *
          (f2 η * g0 (ξ - η) +
            f0 η * g2 (ξ - η)) := by
    exact integral_mono hRawWeighted hInnerMajor hPointwise

  have hNormIntegral :
      ‖h3RawProductConvolution F G ξ‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖ := by
    change
      ‖∫ η : H3FourierPoint3,
          h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖
    exact norm_integral_le_integral_norm _

  calc
    ‖ξ‖ ^ 2 *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      ‖ξ‖ ^ 2 *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        2 *
          (f2 η * g0 (ξ - η) +
            f0 η * g2 (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionSecondMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionSecondMomentMajorant
      unfold h3RawProductConvolutionSecondMomentLeftMajorant
      unfold h3RawProductConvolutionSecondMomentRightMajorant
      dsimp only [f0, g0, f2, g2]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- Numerical second raw Fourier mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionSecondMass_le
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionSecondMass F G
      ≤
    2 *
      (h3SpectralScalarRawFourierSecondMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierSecondMass G) := by
  have hTarget :=
    h3RawProductConvolution_secondMoment_integrable_of
      F G hF2 hG2

  have hMajor :=
    h3RawProductConvolutionSecondMomentMajorant_integrable
      F G hF2 hG2

  have hDom :=
    h3RawProductConvolution_secondMoment_le_majorant_ae
      F G hF2 hG2

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionSecondMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionSecondMomentMajorant F G ξ :=
      hIntegral
    _ =
      2 *
        (h3SpectralScalarRawFourierSecondMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierSecondMass G) :=
      h3RawProductConvolutionSecondMomentMajorant_integral_eq
        F G hF2 hG2

end
end Euclidean
end Bridge
end PrimeTensor
