import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterFrequencySplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarterConvolutionMajorantMass

/-!
# Sixth Fréchet endpoint: nineteen-quarter convolution Young majorant mass

`NineteenQuarterFrequencySplit` gives

    |ξ|^(19/4)
      ≤
    2^(19/4)
      (|η|^(19/4) + |ξ - η|^(19/4)).

This file packages the two resulting scalar Young convolutions and computes
their exact total `L¹` mass.

Writing

    m₀(F)     = ∫ |F̂|,
    m₁₉/₄(F) = ∫ |ξ|^(19/4) |F̂(ξ)|,

the complete `19/4` majorant has exact mass

    2^(19/4)
      (m₁₉/₄(F)m₀(G) + m₀(F)m₁₉/₄(G)).

The actual complex raw convolution is compared with this majorant in the next
checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left `19/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionNineteenQuarterMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (h3FourierNineteenQuarterWeight η *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right `19/4`-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionNineteenQuarterMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (h3FourierNineteenQuarterWeight (ξ - η) *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete `19/4`-moment Young majorant. -/
noncomputable def h3RawProductConvolutionNineteenQuarterMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierNineteenQuarterSplitCoefficient *
    (h3RawProductConvolutionNineteenQuarterMomentLeftMajorant F G ξ +
      h3RawProductConvolutionNineteenQuarterMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable `19/4` raw Fourier moment. -/
theorem h3RawProductConvolutionNineteenQuarterMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineteenQuarterMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF19.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (h3FourierNineteenQuarterWeight η *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable `19/4` raw Fourier moment. -/
theorem h3RawProductConvolutionNineteenQuarterMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineteenQuarterMomentRightMajorant F G)
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
      hG19

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (h3FourierNineteenQuarterWeight (ξ - η) *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar `19/4` convolution majorant is integrable. -/
theorem h3RawProductConvolutionNineteenQuarterMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionNineteenQuarterMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionNineteenQuarterMomentMajorant
  exact
    ((h3RawProductConvolutionNineteenQuarterMomentLeftMajorant_integrable
        F G hF19).add
      (h3RawProductConvolutionNineteenQuarterMomentRightMajorant_integrable
        F G hG19)).const_mul
          h3FourierNineteenQuarterSplitCoefficient

/-- Exact total mass of the left `19/4` Young majorant. -/
theorem h3RawProductConvolutionNineteenQuarterMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineteenQuarterMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierNineteenQuarterMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f19 : H3FourierPoint3 → ℝ :=
    fun η =>
      h3FourierNineteenQuarterWeight η *
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
      hF19
      hG0

  unfold h3RawProductConvolutionNineteenQuarterMomentLeftMajorant
  unfold h3SpectralScalarRawFourierNineteenQuarterMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f19 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f19 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f19 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f19 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f19)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f19 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right `19/4` Young majorant. -/
theorem h3RawProductConvolutionNineteenQuarterMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineteenQuarterMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierNineteenQuarterMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g19 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      h3FourierNineteenQuarterWeight ζ *
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
      hG19

  unfold h3RawProductConvolutionNineteenQuarterMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierNineteenQuarterMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g19 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g19 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g19 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g19 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g19)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g19 ζ := by
      exact hConv

/-- Exact total mass of the complete `19/4` convolution majorant. -/
theorem h3RawProductConvolutionNineteenQuarterMomentMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF19 :
      Integrable
        (fun η : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight η *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG19 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ζ *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionNineteenQuarterMomentMajorant F G ξ)
      =
    h3FourierNineteenQuarterSplitCoefficient *
      (h3SpectralScalarRawFourierNineteenQuarterMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierNineteenQuarterMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionNineteenQuarterMomentLeftMajorant_integrable
      F G hF19

  have hRightInt :=
    h3RawProductConvolutionNineteenQuarterMomentRightMajorant_integrable
      F G hG19

  unfold h3RawProductConvolutionNineteenQuarterMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionNineteenQuarterMomentLeftMajorant_integral_eq
      F G hF19,
    h3RawProductConvolutionNineteenQuarterMomentRightMajorant_integral_eq
      F G hG19
  ]

end
end Euclidean
end Bridge
end PrimeTensor
