import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Selected.Convolution.NineQuarter

/-!
# Quantitative mass of the nine-quarter convolution majorant

`SelectedConvolutionNineQuarter` already proves that the exact raw product
convolution is dominated by an integrable Young majorant.

For the later positive-time uniform bootstrap we need the numerical mass of
that majorant, not only its integrability.

Write

    m₀(F)   = ∫ |F̂|,
    m₉(F)   = ∫ |ξ|^(9/4) |F̂(ξ)|.

The left and right Young majorants are literal convolutions of nonnegative
integrable scalar functions.  Mathlib's `MeasureTheory.integral_convolution`
therefore gives the exact identities

    ∫ Left(F,G)  = m₉(F) m₀(G),
    ∫ Right(F,G) = m₀(F) m₉(G).

Consequently the complete majorant has mass

    2^(9/4) (m₉(F)m₀(G) + m₀(F)m₉(G)).

This is the quantitative coefficient needed before propagating the estimate
through the divergence and Leray sums.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Unweighted raw Fourier `L¹` mass. -/
noncomputable def h3SpectralScalarRawFourierL1Mass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F ξ‖

/-- Raw Fourier `9/4` weighted `L¹` mass. -/
noncomputable def h3SpectralScalarRawFourierNineQuarterMass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierNineQuarterWeight ξ *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- Exact total mass of the left Young majorant. -/
theorem h3RawProductConvolutionNineQuarterMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hFq :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineQuarterMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierNineQuarterMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let fq : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖h3SpectralScalarRawFourier G ζ‖

  have hG0 :
      Integrable g0 (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hFq
      hG0

  unfold h3RawProductConvolutionNineQuarterMomentLeftMajorant
  unfold h3SpectralScalarRawFourierNineQuarterMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        fq η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, fq η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        fq η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          fq g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := fq)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, fq η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right Young majorant. -/
theorem h3RawProductConvolutionNineQuarterMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hGq :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineQuarterMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierNineQuarterMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
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

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hF0
      hGq

  unfold h3RawProductConvolutionNineQuarterMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierNineQuarterMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * gq (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, gq ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * gq (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 gq (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f0)
          (g := gq)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, gq ζ := by
      exact hConv

/-- Exact total mass of the complete `9/4` convolution majorant. -/
theorem h3RawProductConvolutionNineQuarterMomentMajorant_integral_eq
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
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineQuarterMomentMajorant F G ξ)
      =
    h3FourierNineQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierNineQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierNineQuarterMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionNineQuarterMomentLeftMajorant_integrable
      F G hFq

  have hRightInt :=
    h3RawProductConvolutionNineQuarterMomentRightMajorant_integrable
      F G hGq

  unfold h3RawProductConvolutionNineQuarterMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionNineQuarterMomentLeftMajorant_integral_eq
      F G hFq,
    h3RawProductConvolutionNineQuarterMomentRightMajorant_integral_eq
      F G hGq
  ]

end
end Euclidean
end Bridge
end PrimeTensor
