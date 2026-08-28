import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.FourthFrequencySplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterConvolutionMajorantMass

/-!
# Sixth Fréchet endpoint: fourth convolution Young majorant mass

`FourthFrequencySplit` gives the output-frequency inequality

    |ξ|^4
      ≤
    2^4 (|η|^4 + |ξ - η|^4).

This file packages the two resulting scalar Young convolutions and computes
their exact total `L¹` mass.

Writing

    m₀(F) = ∫ |F̂|,
    m₄(F) = ∫ |ξ|^4 |F̂(ξ)|,

the complete fourth-moment majorant has exact mass

    2^4 (m₄(F)m₀(G) + m₀(F)m₄(G)).

As in the preceding endpoint layers, the actual complex raw convolution is not
compared with this scalar majorant here.  That pointwise domination and the
resulting selected convolution mass estimate are the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointFourthConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left fourth-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFourthMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (‖η‖ ^ 4 *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right fourth-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFourthMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (‖ξ - η‖ ^ 4 *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete fourth-moment Young majorant. -/
noncomputable def h3RawProductConvolutionFourthMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierFourthSplitCoefficient *
    (h3RawProductConvolutionFourthMomentLeftMajorant F G ξ +
      h3RawProductConvolutionFourthMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable fourth raw Fourier moment. -/
theorem h3RawProductConvolutionFourthMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFourthMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF4.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (‖η‖ ^ 4 *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable fourth raw Fourier moment. -/
theorem h3RawProductConvolutionFourthMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFourthMomentRightMajorant F G)
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
      hG4

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (‖ξ - η‖ ^ 4 *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar fourth-moment convolution majorant is integrable. -/
theorem h3RawProductConvolutionFourthMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFourthMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionFourthMomentMajorant
  exact
    ((h3RawProductConvolutionFourthMomentLeftMajorant_integrable
        F G hF4).add
      (h3RawProductConvolutionFourthMomentRightMajorant_integrable
        F G hG4)).const_mul
          h3FourierFourthSplitCoefficient

/-- Exact total mass of the left fourth-moment Young majorant. -/
theorem h3RawProductConvolutionFourthMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFourthMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierFourthMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f4 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 4 *
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
      hF4
      hG0

  unfold h3RawProductConvolutionFourthMomentLeftMajorant
  unfold h3SpectralScalarRawFourierFourthMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f4 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f4 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f4 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f4 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f4)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f4 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right fourth-moment Young majorant. -/
theorem h3RawProductConvolutionFourthMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFourthMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierFourthMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g4 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 4 *
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
      hG4

  unfold h3RawProductConvolutionFourthMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierFourthMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g4 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g4 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g4 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g4 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g4)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g4 ζ := by
      exact hConv

/-- Exact total mass of the complete fourth-moment convolution majorant. -/
theorem h3RawProductConvolutionFourthMomentMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF4 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 4 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG4 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 4 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFourthMomentMajorant F G ξ)
      =
    h3FourierFourthSplitCoefficient *
      (h3SpectralScalarRawFourierFourthMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFourthMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionFourthMomentLeftMajorant_integrable
      F G hF4

  have hRightInt :=
    h3RawProductConvolutionFourthMomentRightMajorant_integrable
      F G hG4

  unfold h3RawProductConvolutionFourthMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionFourthMomentLeftMajorant_integral_eq
      F G hF4,
    h3RawProductConvolutionFourthMomentRightMajorant_integral_eq
      F G hG4
  ]

end
end Euclidean
end Bridge
end PrimeTensor
