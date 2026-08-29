import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Seventh.Endpoint.FifthFrequencySplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterConvolutionMajorantMass

/-!
# Seventh Fréchet endpoint: fifth convolution Young majorant mass

`FifthFrequencySplit` gives the output-frequency inequality

    |ξ|^5
      ≤
    2^5 (|η|^5 + |ξ - η|^5).

This file packages the two resulting scalar Young convolutions and computes
their exact total `L¹` mass.

Writing

    m₀(F) = ∫ |F̂|,
    m₅(F) = ∫ |ξ|^5 |F̂(ξ)|,

the complete fifth-moment majorant has exact mass

    2^5 (m₅(F)m₀(G) + m₀(F)m₅(G)).

As in the preceding endpoint layers, the actual complex raw convolution is not
compared with this scalar majorant here. That pointwise domination and the
resulting selected convolution mass estimate are the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSeventhEndpointFifthConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left fifth-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFifthMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (‖η‖ ^ 5 *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right fifth-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFifthMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (‖ξ - η‖ ^ 5 *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete fifth-moment Young majorant. -/
noncomputable def h3RawProductConvolutionFifthMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierFifthSplitCoefficient *
    (h3RawProductConvolutionFifthMomentLeftMajorant F G ξ +
      h3RawProductConvolutionFifthMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable fifth raw Fourier moment. -/
theorem h3RawProductConvolutionFifthMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifthMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF5.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (‖η‖ ^ 5 *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable fifth raw Fourier moment. -/
theorem h3RawProductConvolutionFifthMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifthMomentRightMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hF0 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hConv :=
    hF0.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG5

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (‖ξ - η‖ ^ 5 *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar fifth-moment convolution majorant is integrable. -/
theorem h3RawProductConvolutionFifthMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifthMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionFifthMomentMajorant
  exact
    ((h3RawProductConvolutionFifthMomentLeftMajorant_integrable
        F G hF5).add
      (h3RawProductConvolutionFifthMomentRightMajorant_integrable
        F G hG5)).const_mul
          h3FourierFifthSplitCoefficient

/-- Exact total mass of the left fifth-moment Young majorant. -/
theorem h3RawProductConvolutionFifthMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifthMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierFifthMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f5 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 5 *
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
      hF5
      hG0

  unfold h3RawProductConvolutionFifthMomentLeftMajorant
  unfold h3SpectralScalarRawFourierFifthMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f5 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f5 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f5 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f5 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f5)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f5 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right fifth-moment Young majorant. -/
theorem h3RawProductConvolutionFifthMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifthMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierFifthMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g5 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 5 *
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
      hG5

  unfold h3RawProductConvolutionFifthMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierFifthMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g5 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g5 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g5 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g5 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g5)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g5 ζ := by
      exact hConv

/-- Exact total mass of the complete fifth-moment convolution majorant. -/
theorem h3RawProductConvolutionFifthMomentMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF5 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 5 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 5 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifthMomentMajorant F G ξ)
      =
    h3FourierFifthSplitCoefficient *
      (h3SpectralScalarRawFourierFifthMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFifthMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionFifthMomentLeftMajorant_integrable
      F G hF5

  have hRightInt :=
    h3RawProductConvolutionFifthMomentRightMajorant_integrable
      F G hG5

  unfold h3RawProductConvolutionFifthMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionFifthMomentLeftMajorant_integral_eq
      F G hF5,
    h3RawProductConvolutionFifthMomentRightMajorant_integral_eq
      F G hG5
  ]

end
end Euclidean
end Bridge
end PrimeTensor
