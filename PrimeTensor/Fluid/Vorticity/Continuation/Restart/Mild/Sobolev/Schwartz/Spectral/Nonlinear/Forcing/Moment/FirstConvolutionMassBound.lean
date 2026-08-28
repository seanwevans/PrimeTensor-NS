import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SecondConvolutionMassBound

/-!
# Quantitative zeroth and first masses of the exact raw convolution

The frozen `9/4` endpoint ultimately needs a quantitative zeroth forcing mass
in addition to the first forcing mass already closed.

A divergence derivative at zeroth forcing weight consumes the first raw
convolution moment.  This file closes that scalar input from the same state
data already available.

First, Young gives the exact zeroth-mass estimate

    m₀(F * G) ≤ m₀(F) m₀(G).

Second, for every radial frequency `r ≥ 0`,

    r ≤ 1 + r².

Hence

    m₁(F * G)
      ≤
    m₀(F * G) + m₂(F * G),

and `SecondConvolutionMassBound` supplies

    m₂(F * G)
      ≤
    2 (m₂(F)m₀(G) + m₀(F)m₂(G)).

Therefore

    m₁(F * G)
      ≤
    m₀(F)m₀(G)
      + 2 (m₂(F)m₀(G) + m₀(F)m₂(G)).

No new state regularity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFirstConvolutionMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Zeroth raw Fourier `L¹` mass of the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionL1Mass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖h3RawProductConvolution F G ξ‖

/-- Scalar Young majorant for the zeroth raw convolution mass. -/
noncomputable def h3RawProductConvolutionL1Majorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- The zeroth scalar Young majorant is integrable. -/
theorem h3RawProductConvolutionL1Majorant_integrable
    (F G : H3SpectralScalarState) :
    Integrable
      (h3RawProductConvolutionL1Majorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hF0 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 F)).norm

  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF0.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- Exact total mass of the zeroth scalar Young majorant. -/
theorem h3RawProductConvolutionL1Majorant_integral_eq
    (F G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionL1Majorant F G ξ)
      =
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierL1Mass G := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖

  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖

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

  have hConv :=
    MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hF0
      hG0

  unfold h3RawProductConvolutionL1Majorant
  unfold h3SpectralScalarRawFourierL1Mass

  change
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g0 (ξ - η))
      =
    (∫ η : H3FourierPoint3, f0 η) *
      ∫ ζ : H3FourierPoint3, g0 ζ

  calc
    (∫ ξ : H3FourierPoint3,
      ∫ η : H3FourierPoint3,
        f0 η * g0 (ξ - η))
        =
      ∫ ξ : H3FourierPoint3,
        MeasureTheory.convolution
          f0 g0 (ContinuousLinearMap.mul ℝ ℝ)
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
          (g := g0)
          (x := ξ)
    _ =
      (∫ η : H3FourierPoint3, f0 η) *
        ∫ ζ : H3FourierPoint3, g0 ζ := by
      exact hConv

/-- Pointwise norm domination by the zeroth scalar Young majorant. -/
theorem h3RawProductConvolution_norm_le_L1Majorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3RawProductConvolution F G ξ‖
      ≤
    h3RawProductConvolutionL1Majorant F G ξ := by
  unfold h3RawProductConvolution
  unfold h3RawProductConvolutionL1Majorant

  change
    ‖∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖
      ≤
    ∫ η : H3FourierPoint3,
      ‖h3SpectralScalarRawFourier F η‖ *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖

  calc
    ‖∫ η : H3FourierPoint3,
        h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖
        ≤
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η *
          h3SpectralScalarRawFourier G (ξ - η)‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ η : H3FourierPoint3,
        ‖h3SpectralScalarRawFourier F η‖ *
          ‖h3SpectralScalarRawFourier G (ξ - η)‖ := by
      apply integral_congr_ae
      filter_upwards with η
      rw [norm_mul]

/-- Numerical Young bound for the actual zeroth raw convolution mass. -/
theorem h3RawProductConvolutionL1Mass_le
    (F G : H3SpectralScalarState) :
    h3RawProductConvolutionL1Mass F G
      ≤
    h3SpectralScalarRawFourierL1Mass F *
      h3SpectralScalarRawFourierL1Mass G := by
  have hTarget :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawProductConvolution_integrable F G).norm

  have hMajor :=
    h3RawProductConvolutionL1Majorant_integrable F G

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖h3RawProductConvolution F G ξ‖
          ≤
        h3RawProductConvolutionL1Majorant F G ξ :=
    Filter.Eventually.of_forall
      (h3RawProductConvolution_norm_le_L1Majorant F G)

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3RawProductConvolutionL1Majorant F G ξ :=
      hIntegral
    _ =
      h3SpectralScalarRawFourierL1Mass F *
        h3SpectralScalarRawFourierL1Mass G :=
      h3RawProductConvolutionL1Majorant_integral_eq F G

/-- First raw Fourier mass of the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionFirstMass
    (F G : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    ‖ξ‖ *
      ‖h3RawProductConvolution F G ξ‖

/-- The radial first weight is bounded by zeroth plus second weight. -/
theorem norm_le_one_add_norm_sq
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

/-- The first convolution mass is bounded by the sum of its zeroth and second
masses. -/
theorem h3RawProductConvolutionFirstMass_le_L1Mass_add_secondMass
    (F G : H3SpectralScalarState)
    (hConv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionFirstMass F G
      ≤
    h3RawProductConvolutionL1Mass F G +
      h3RawProductConvolutionSecondMass F G := by
  have hTarget :=
    h3RawProductConvolution_firstMoment_integrable F G

  have hZero :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (h3RawProductConvolution_integrable F G).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖h3RawProductConvolution F G ξ‖ +
            ‖ξ‖ ^ 2 *
              ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hZero.add hConv2

  have hDom :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ‖ξ‖ *
            ‖h3RawProductConvolution F G ξ‖
          ≤
        ‖h3RawProductConvolution F G ξ‖ +
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖ := by
    filter_upwards with ξ

    have hNormConv :
        0 ≤ ‖h3RawProductConvolution F G ξ‖ :=
      norm_nonneg _

    calc
      ‖ξ‖ *
          ‖h3RawProductConvolution F G ξ‖
          ≤
        (1 + ‖ξ‖ ^ 2) *
          ‖h3RawProductConvolution F G ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_le_one_add_norm_sq ξ)
          hNormConv
      _ =
        ‖h3RawProductConvolution F G ξ‖ +
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖ := by
        ring

  have hIntegral :=
    integral_mono_ae hTarget hMajor hDom

  unfold h3RawProductConvolutionFirstMass
  unfold h3RawProductConvolutionL1Mass
  unfold h3RawProductConvolutionSecondMass

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawProductConvolution F G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (‖h3RawProductConvolution F G ξ‖ +
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖) :=
      hIntegral
    _ =
      (∫ ξ : H3FourierPoint3,
          ‖h3RawProductConvolution F G ξ‖) +
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖ := by
      rw [integral_add hZero hConv2]

/-- Fully quantitative first convolution mass in terms of zeroth and second
state masses. -/
theorem h3RawProductConvolutionFirstMass_le_stateMasses
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    h3RawProductConvolutionFirstMass F G
      ≤
    h3SpectralScalarRawFourierL1Mass F *
        h3SpectralScalarRawFourierL1Mass G
      +
    2 *
      (h3SpectralScalarRawFourierSecondMass F *
          h3SpectralScalarRawFourierL1Mass G +
        h3SpectralScalarRawFourierL1Mass F *
          h3SpectralScalarRawFourierSecondMass G) := by
  have hConv2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawProductConvolution_secondMoment_integrable_of
      F G hF2 hG2

  have hFirst :=
    h3RawProductConvolutionFirstMass_le_L1Mass_add_secondMass
      F G hConv2

  have hZero :=
    h3RawProductConvolutionL1Mass_le F G

  have hSecond :=
    h3RawProductConvolutionSecondMass_le
      F G hF2 hG2

  exact
    le_trans hFirst
      (add_le_add hZero hSecond)

end
end Euclidean
end Bridge
end PrimeTensor
