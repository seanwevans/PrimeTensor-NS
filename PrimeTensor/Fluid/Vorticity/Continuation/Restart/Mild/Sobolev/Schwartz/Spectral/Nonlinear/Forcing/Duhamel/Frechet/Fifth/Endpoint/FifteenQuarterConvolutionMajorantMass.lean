import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterFrequencySplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterConvolutionMajorantMass

/-!
# Fifth Fréchet endpoint: fifteen-quarter convolution Young majorant mass

`FifteenQuarterFrequencySplit` gives the fractional output-frequency inequality

    |ξ|^(15/4)
      ≤
    2^(15/4)
      (|η|^(15/4) + |ξ - η|^(15/4)).

This file packages the two resulting scalar Young convolutions and computes
their exact total `L¹` mass.

Writing

    m₀(F)     = ∫ |F̂|,
    m₁₅/₄(F) = ∫ |ξ|^(15/4) |F̂(ξ)|,

the complete `15/4` majorant has exact mass

    2^(15/4)
      (m₁₅/₄(F)m₀(G) + m₀(F)m₁₅/₄(G)).

As in the cubic layer, the actual complex raw convolution is not compared with
this scalar majorant here.  That pointwise domination and the resulting
convolution mass estimate are the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left `15/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFifteenQuarterMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (h3FourierFifteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right `15/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFifteenQuarterMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (h3FourierFifteenQuarterWeight (ξ - η) *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete `15/4`-moment Young majorant. -/
noncomputable def h3RawProductConvolutionFifteenQuarterMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierFifteenQuarterSplitCoefficient *
    (h3RawProductConvolutionFifteenQuarterMomentLeftMajorant F G ξ +
      h3RawProductConvolutionFifteenQuarterMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable `15/4` raw Fourier moment. -/
theorem h3RawProductConvolutionFifteenQuarterMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifteenQuarterMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF15.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (h3FourierFifteenQuarterWeight η *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable `15/4` raw Fourier moment. -/
theorem h3RawProductConvolutionFifteenQuarterMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifteenQuarterMomentRightMajorant F G)
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
      hG15

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (h3FourierFifteenQuarterWeight (ξ - η) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar `15/4` convolution majorant is integrable. -/
theorem h3RawProductConvolutionFifteenQuarterMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionFifteenQuarterMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionFifteenQuarterMomentMajorant
  exact
    ((h3RawProductConvolutionFifteenQuarterMomentLeftMajorant_integrable
        F G hF15).add
      (h3RawProductConvolutionFifteenQuarterMomentRightMajorant_integrable
        F G hG15)).const_mul
          h3FourierFifteenQuarterSplitCoefficient

/-- Exact total mass of the left `15/4` Young majorant. -/
theorem h3RawProductConvolutionFifteenQuarterMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifteenQuarterMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierFifteenQuarterMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f15 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierFifteenQuarterWeight η *
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
      hF15
      hG0

  unfold h3RawProductConvolutionFifteenQuarterMomentLeftMajorant
  unfold h3SpectralScalarRawFourierFifteenQuarterMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f15 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f15 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f15 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f15 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f15)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f15 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right `15/4` Young majorant. -/
theorem h3RawProductConvolutionFifteenQuarterMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifteenQuarterMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierFifteenQuarterMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g15 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierFifteenQuarterWeight ζ *
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
      hG15

  unfold h3RawProductConvolutionFifteenQuarterMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierFifteenQuarterMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g15 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g15 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g15 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g15 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g15)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g15 ζ := by
      exact hConv

/-- Exact total mass of the complete `15/4` convolution majorant. -/
theorem h3RawProductConvolutionFifteenQuarterMomentMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF15 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG15 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionFifteenQuarterMomentMajorant F G ξ)
      =
    h3FourierFifteenQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierFifteenQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierFifteenQuarterMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionFifteenQuarterMomentLeftMajorant_integrable
      F G hF15

  have hRightInt :=
    h3RawProductConvolutionFifteenQuarterMomentRightMajorant_integrable
      F G hG15

  unfold h3RawProductConvolutionFifteenQuarterMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionFifteenQuarterMomentLeftMajorant_integral_eq
      F G hF15,
    h3RawProductConvolutionFifteenQuarterMomentRightMajorant_integral_eq
      F G hG15
  ]

end
end Euclidean
end Bridge
end PrimeTensor
