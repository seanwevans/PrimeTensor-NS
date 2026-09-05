import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Second.Mild.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.Selected.Convolution.Second

/-!
# Quantitative mass of the second-moment convolution majorant

`SelectedConvolutionSecond` already proves that the exact raw product
convolution is dominated by the scalar Young majorant

    2 ((|·|² |F̂|) * |Ĝ| + |F̂| * (|·|² |Ĝ|)).

`SecondMildMass` exposes the numerical scalar state mass

    m₂(F) = ∫ |ξ|² |F̂(ξ)|.

This file computes the exact total mass of the two Young majorants using
`MeasureTheory.integral_convolution`:

    ∫ Left₂(F,G)  = m₂(F) m₀(G),
    ∫ Right₂(F,G) = m₀(F) m₂(G),

hence

    ∫ Majorant₂(F,G)
      =
    2 (m₂(F)m₀(G) + m₀(F)m₂(G)).

The next layer can therefore turn the already-established pointwise domination
into a numerical second-moment bound for the exact raw convolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSecondConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Exact total mass of the left second-moment Young majorant. -/
theorem h3RawProductConvolutionSecondMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionSecondMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierSecondMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f2 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 2 *
        ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖h3SpectralScalarRawFourier G ζ‖

  have hG0 :
      Integrable
        g0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [g0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hF2
      hG0

  unfold h3RawProductConvolutionSecondMomentLeftMajorant
  unfold h3SpectralScalarRawFourierSecondMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f2 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f2 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f2 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f2 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f2)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f2 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right second-moment Young majorant. -/
theorem h3RawProductConvolutionSecondMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionSecondMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierSecondMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g2 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 2 *
        ‖h3SpectralScalarRawFourier G ζ‖

  have hF0 :
      Integrable
        f0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f0]
    exact
      (MeasureTheory.memLp_one_iff_integrable.mp
        (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hF0
      hG2

  unfold h3RawProductConvolutionSecondMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierSecondMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g2 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g2 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g2 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g2 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g2)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g2 ζ := by
      exact hConv

/-- Exact total mass of the complete second-moment convolution majorant. -/
theorem h3RawProductConvolutionSecondMomentMajorant_integral_eq
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
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionSecondMomentMajorant F G ξ)
      =
    2 *
      (h3SpectralScalarRawFourierSecondMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierSecondMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionSecondMomentLeftMajorant_integrable
      F G hF2

  have hRightInt :=
    h3RawProductConvolutionSecondMomentRightMajorant_integrable
      F G hG2

  unfold h3RawProductConvolutionSecondMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionSecondMomentLeftMajorant_integral_eq
      F G hF2,
    h3RawProductConvolutionSecondMomentRightMajorant_integral_eq
      F G hG2
  ]

end
end Euclidean
end Bridge
end PrimeTensor
