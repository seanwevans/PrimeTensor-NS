import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Third.Frequency.Split
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.NineQuarter.Convolution.Majorant.Mass

/-!
# Fifth Fréchet endpoint: cubic convolution Young majorant mass

`ThirdFrequencySplit` gives the cubic output-frequency inequality

    ‖ξ‖³ ≤ 4 (‖η‖³ + ‖ξ - η‖³).

This file packages the two resulting scalar Young convolutions and computes
their exact total `L¹` mass.

Writing

    m₀(F) = ∫ |F̂|,
    m₃(F) = ∫ |ξ|³ |F̂(ξ)|,

the complete cubic majorant has exact mass

    4 (m₃(F)m₀(G) + m₀(F)m₃(G)).

The actual raw convolution is not yet compared with this majorant here; that
pointwise domination is the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointThirdConvolutionMajorantMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left cubic-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionThirdMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (‖η‖ ^ 3 *
        ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right cubic-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionThirdMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (‖ξ - η‖ ^ 3 *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete cubic-moment Young majorant. -/
noncomputable def h3RawProductConvolutionThirdMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  h3FourierThirdSplitCoefficient *
    (h3RawProductConvolutionThirdMomentLeftMajorant F G ξ +
      h3RawProductConvolutionThirdMomentRightMajorant F G ξ)

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable cubic raw Fourier moment. -/
theorem h3RawProductConvolutionThirdMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionThirdMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF3.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (‖η‖ ^ 3 *
              ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input
has an integrable cubic raw Fourier moment. -/
theorem h3RawProductConvolutionThirdMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionThirdMomentRightMajorant F G)
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
      hG3

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (‖ξ - η‖ ^ 3 *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar cubic convolution majorant is integrable. -/
theorem h3RawProductConvolutionThirdMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionThirdMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionThirdMomentMajorant
  exact
    ((h3RawProductConvolutionThirdMomentLeftMajorant_integrable
        F G hF3).add
      (h3RawProductConvolutionThirdMomentRightMajorant_integrable
        F G hG3)).const_mul
          h3FourierThirdSplitCoefficient

/-- Exact total mass of the left cubic Young majorant. -/
theorem h3RawProductConvolutionThirdMomentLeftMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionThirdMomentLeftMajorant F G ξ)
      =
    h3SpectralScalarRawFourierThirdMass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f3 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖η‖ ^ 3 *
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
      hF3
      hG0

  unfold h3RawProductConvolutionThirdMomentLeftMajorant
  unfold h3SpectralScalarRawFourierThirdMass
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f3 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f3 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f3 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f3 g0 (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure H3FourierPoint3) ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      symm
      exact
        MeasureTheory.convolution_mul
          (𝕜 := ℝ)
          (G := H3FourierPoint3)
          (μ := (volume : Measure H3FourierPoint3))
          (f := f3)
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f3 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Exact total mass of the right cubic Young majorant. -/
theorem h3RawProductConvolutionThirdMomentRightMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionThirdMomentRightMajorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierThirdMass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η =>
      ‖h3SpectralScalarRawFourier F η‖

  let g3 : H3FourierPoint3 → ℝ :=
    fun ζ =>
      ‖ζ‖ ^ 3 *
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
      hG3

  unfold h3RawProductConvolutionThirdMomentRightMajorant
  unfold h3SpectralScalarRawFourierL1Mass
  unfold h3SpectralScalarRawFourierThirdMass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g3 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g3 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g3 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g3 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g3)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g3 ζ := by
      exact hConv

/-- Exact total mass of the complete cubic convolution majorant. -/
theorem h3RawProductConvolutionThirdMomentMajorant_integral_eq
    (F G : H3SpectralScalarState)
    (hF3 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 3 *
            ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG3 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 3 *
            ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionThirdMomentMajorant F G ξ)
      =
    h3FourierThirdSplitCoefficient *
      (h3SpectralScalarRawFourierThirdMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierThirdMass G) := by
  have hLeftInt :=
    h3RawProductConvolutionThirdMomentLeftMajorant_integrable
      F G hF3

  have hRightInt :=
    h3RawProductConvolutionThirdMomentRightMajorant_integrable
      F G hG3

  unfold h3RawProductConvolutionThirdMomentMajorant

  rw [integral_const_mul]
  rw [integral_add hLeftInt hRightInt]
  rw [
    h3RawProductConvolutionThirdMomentLeftMajorant_integral_eq
      F G hF3,
    h3RawProductConvolutionThirdMomentRightMajorant_integral_eq
      F G hG3
  ]

end
end Euclidean
end Bridge
end PrimeTensor
