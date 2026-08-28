import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterConvolutionMajorantMass

/-!
# Quantitative nine-quarter mass bound for the exact raw convolution

`NineQuarterConvolutionMajorantMass` computes the exact total mass of the Young
majorant already used by `SelectedConvolutionNineQuarter`.

The remaining step is to expose the pointwise domination that was previously
local to the qualitative integrability proof:

    |ξ|^(9/4) |(F̂ * Ĝ)(ξ)|
      ≤
    M₉(F,G)(ξ)

for almost every frequency.

Integrating this named domination and rewriting the exact majorant mass gives

    ∫ |ξ|^(9/4) |(F̂ * Ĝ)(ξ)|
      ≤
    2^(9/4) (m₉(F)m₀(G) + m₀(F)m₉(G)).

This is the numerical convolution estimate needed by the later forcing-mass
bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterConvolutionMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Actual raw-product-convolution `9/4` weighted `L¹` mass. -/
noncomputable def h3RawProductConvolutionNineQuarterMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierNineQuarterWeight ξ *
      ‖h3RawProductConvolution F G ξ‖

/-- The exact raw convolution is dominated almost everywhere by the same
`9/4` Young majorant used in the qualitative integrability proof. -/
theorem h3RawProductConvolution_nineQuarterMoment_le_majorant_ae
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
      h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionNineQuarterMomentMajorant F G ξ := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

  let fq : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let gq : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierNineQuarterWeight ζ *
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
          fq p.2 * g0 (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hFq.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hG0
    simpa only [
      fq, g0,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hRightProd :
      Integrable
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          f0 p.2 * gq (p.1 - p.2))
        ((volume : Measure H3FourierPoint3).prod
          (volume : Measure H3FourierPoint3)) := by
    have h :=
      hF0.convolution_integrand
        (ContinuousLinearMap.mul ℝ ℝ)
        hGq
    simpa only [
      f0, gq,
      ContinuousLinearMap.mul_apply'
    ] using h

  have hLeftAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            fq η * g0 (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hLeftProd.prod_right_ae

  have hRightAE :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Integrable
          (fun η : H3FourierPoint3 =>
            f0 η * gq (ξ - η))
          (volume : Measure H3FourierPoint3) :=
    hRightProd.prod_right_ae

  filter_upwards [hLeftAE, hRightAE] with ξ hLeftξ hRightξ

  have hw :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

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
          h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖)
        (volume : Measure H3FourierPoint3) :=
    hRawKernel.norm.const_mul
      (h3FourierNineQuarterWeight ξ)

  have hInnerMajor :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterSplitCoefficient *
            (fq η * g0 (ξ - η) +
              f0 η * gq (ξ - η)))
        (volume : Measure H3FourierPoint3) :=
    (hLeftξ.add hRightξ).const_mul
      h3FourierNineQuarterSplitCoefficient

  have hPointwise :
      ∀ η : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier F η *
              h3SpectralScalarRawFourier G (ξ - η)‖
          ≤
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
    intro η

    have hFreq :=
      h3FourierNineQuarterWeight_le_split ξ η

    have hProdNonneg :
        0 ≤
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      positivity

    calc
      h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖
          =
        h3FourierNineQuarterWeight ξ *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) := by
              rw [norm_mul]
      _ ≤
        (h3FourierNineQuarterSplitCoefficient *
          (h3FourierNineQuarterWeight η +
            h3FourierNineQuarterWeight (ξ - η))) *
          (‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖) :=
        mul_le_mul_of_nonneg_right hFreq hProdNonneg
      _ =
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
        dsimp only [f0, g0, fq, gq]
        ring

  have hIntegralLe :
      (∫ η : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖)
        ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) := by
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
    h3FourierNineQuarterWeight ξ *
        ‖h3RawProductConvolution F G ξ‖
        ≤
      h3FourierNineQuarterWeight ξ *
        (∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖) :=
      mul_le_mul_of_nonneg_left hNormIntegral hw
    _ =
      ∫ η : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier F η *
            h3SpectralScalarRawFourier G (ξ - η)‖ := by
      rw [integral_const_mul]
    _ ≤
      ∫ η : H3FourierPoint3,
        h3FourierNineQuarterSplitCoefficient *
          (fq η * g0 (ξ - η) +
            f0 η * gq (ξ - η)) :=
      hIntegralLe
    _ =
      h3RawProductConvolutionNineQuarterMomentMajorant F G ξ := by
      unfold h3RawProductConvolutionNineQuarterMomentMajorant
      unfold h3RawProductConvolutionNineQuarterMomentLeftMajorant
      unfold h3RawProductConvolutionNineQuarterMomentRightMajorant
      dsimp only [f0, g0, fq, gq]
      rw [← integral_add hLeftξ hRightξ]
      rw [← integral_const_mul]

/-- Numerical `9/4` weighted `L¹` mass bound for the exact raw product
convolution. -/
theorem h3RawProductConvolutionNineQuarterMass_le
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionNineQuarterMass F G
      ≤
    h3FourierNineQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierNineQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierNineQuarterMass G) := by
  have hTarget :=
    h3RawProductConvolution_nineQuarterMoment_integrable_of
      F G hFq hGq

  have hMajor :=
    h3RawProductConvolutionNineQuarterMomentMajorant_integrable
      F G hFq hGq

  have hDom :=
    h3RawProductConvolution_nineQuarterMoment_le_majorant_ae
      F G hFq hGq

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineQuarterMomentMajorant F G ξ :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionNineQuarterMass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineQuarterMomentMajorant F G ξ :=
      hIntegral
    _ =
      h3FourierNineQuarterSplitCoefficient *
        (h3SpectralScalarRawFourierNineQuarterMass F *
            h3SpectralScalarRawFourierL1Mass G +
          h3SpectralScalarRawFourierL1Mass F *
            h3SpectralScalarRawFourierNineQuarterMass G) :=
      h3RawProductConvolutionNineQuarterMomentMajorant_integral_eq
        F G hFq hGq

end
end Euclidean
end Bridge
end PrimeTensor
