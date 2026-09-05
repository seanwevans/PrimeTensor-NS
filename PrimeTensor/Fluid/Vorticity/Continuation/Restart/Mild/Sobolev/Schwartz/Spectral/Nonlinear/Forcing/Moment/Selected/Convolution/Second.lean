import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Mild.Raw.Second
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1
import Mathlib.Analysis.Convolution

/-!
# Second raw Fourier moment of the selected nonlinear convolution

The selected positive-time mild state now has an integrable second moment in
the canonical raw Fourier representative used by `h3RawProductConvolution`.

This file proves the nonlinear propagation step at the convolution level.

For arbitrary H³ spectral scalar states `F`, `G`, assume that both canonical
raw representatives have an integrable second Fourier moment.  The elementary
frequency split

    ‖ξ‖² ≤ 2 (‖η‖² + ‖ξ - η‖²)

gives the convolution majorant

    ‖ξ‖² |(f̂ * ĝ)(ξ)|
      ≤
    2 ((|·|² |f̂|) * |ĝ|)(ξ)
      + 2 (|f̂| * (|·|² |ĝ|))(ξ).

The two scalar majorants are genuine `L¹` convolutions.  Mathlib's
`Integrable.integrable_convolution` therefore makes the output majorant
integrable.  The exact raw convolution is then dominated almost everywhere by
that majorant.

Specializing to two coordinates of the selected positive-time mild state gives
the second raw Fourier moment needed before spending one power of frequency on
the divergence derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter ContinuousLinearMap
open scoped ENNReal NNReal Interval Topology InnerProductSpace Convolution

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedRawConvolutionSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Left second-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionSecondMomentLeftMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    (‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖) *
      ‖h3SpectralScalarRawFourier G (ξ - η)‖

/-- Right second-moment Young majorant for the exact raw product convolution. -/
noncomputable def h3RawProductConvolutionSecondMomentRightMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  ∫ η : H3FourierPoint3,
    ‖h3SpectralScalarRawFourier F η‖ *
      (‖ξ - η‖ ^ 2 *
        ‖h3SpectralScalarRawFourier G (ξ - η)‖)

/-- Complete second-moment Young majorant. -/
noncomputable def h3RawProductConvolutionSecondMomentMajorant
    (F G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℝ :=
  2 *
    (h3RawProductConvolutionSecondMomentLeftMajorant F G ξ +
      h3RawProductConvolutionSecondMomentRightMajorant F G ξ)

/-- The Euclidean output frequency splits into the convolution parameter and
the translated frequency with the standard quadratic bound. -/
theorem h3FourierNorm_sq_le_two_sq_add_sq
    (ξ η : H3FourierPoint3) :
    ‖ξ‖ ^ 2 ≤ 2 * (‖η‖ ^ 2 + ‖ξ - η‖ ^ 2) := by
  have htri :
      ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    calc
      ‖ξ‖ = ‖η + (ξ - η)‖ := by
        congr 1
        abel
      _ ≤ ‖η‖ + ‖ξ - η‖ :=
        norm_add_le _ _

  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hη0 : 0 ≤ ‖η‖ := norm_nonneg _
  have hshift0 : 0 ≤ ‖ξ - η‖ := norm_nonneg _

  have hsq :
      ‖ξ‖ ^ 2 ≤ (‖η‖ + ‖ξ - η‖) ^ 2 := by
    nlinarith

  have hsum :
      (‖η‖ + ‖ξ - η‖) ^ 2
        ≤ 2 * (‖η‖ ^ 2 + ‖ξ - η‖ ^ 2) := by
    nlinarith [sq_nonneg (‖η‖ - ‖ξ - η‖)]

  exact hsq.trans hsum

/-- The left scalar Young majorant is integrable whenever the first input has
an integrable second raw moment. -/
theorem h3RawProductConvolutionSecondMomentLeftMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionSecondMomentLeftMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  have hG0 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3) :=
    (MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)).norm

  have hConv :=
    hF2.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ)
      hG0

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          (‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖) *
            ‖h3SpectralScalarRawFourier G (ξ - η)‖)
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The right scalar Young majorant is integrable whenever the second input has
an integrable second raw moment. -/
theorem h3RawProductConvolutionSecondMomentRightMajorant_integrable
    (F G : H3SpectralScalarState)
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionSecondMomentRightMajorant F G)
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
      hG2

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ∫ η : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier F η‖ *
            (‖ξ - η‖ ^ 2 *
              ‖h3SpectralScalarRawFourier G (ξ - η)‖))
      (volume : Measure H3FourierPoint3)

  exact hConv

/-- The complete scalar second-moment majorant is integrable. -/
theorem h3RawProductConvolutionSecondMomentMajorant_integrable
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (h3RawProductConvolutionSecondMomentMajorant F G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawProductConvolutionSecondMomentMajorant
  exact
    ((h3RawProductConvolutionSecondMomentLeftMajorant_integrable
        F G hF2).add
      (h3RawProductConvolutionSecondMomentRightMajorant_integrable
        F G hG2)).const_mul 2

/-- The exact raw convolution inherits an integrable second Fourier moment from
second moments on both input raw representatives. -/
theorem h3RawProductConvolution_secondMoment_integrable_of
    (F G : H3SpectralScalarState)
    (hF2 :
      Integrable
        (fun η : H3FourierPoint3 =>
          ‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖)
        (volume : Measure H3FourierPoint3))
    (hG2 :
      Integrable
        (fun ζ : H3FourierPoint3 =>
          ‖ζ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ζ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let f0 : H3FourierPoint3 → ℝ :=
    fun η => ‖h3SpectralScalarRawFourier F η‖
  let g0 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖h3SpectralScalarRawFourier G ζ‖
  let f2 : H3FourierPoint3 → ℝ :=
    fun η => ‖η‖ ^ 2 * ‖h3SpectralScalarRawFourier F η‖
  let g2 : H3FourierPoint3 → ℝ :=
    fun ζ => ‖ζ‖ ^ 2 * ‖h3SpectralScalarRawFourier G ζ‖

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

  have hMajor :=
    h3RawProductConvolutionSecondMomentMajorant_integrable
      F G hF2 hG2

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((continuous_norm.pow 2).aestronglyMeasurable).mul
        (h3RawProductConvolution_integrable F G).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_

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

  have hBound :
      ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖
        ≤
      h3RawProductConvolutionSecondMomentMajorant F G ξ := by
    calc
      ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖
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

  have hTargetNonneg :
      0 ≤ ‖ξ‖ ^ 2 * ‖h3RawProductConvolution F G ξ‖ := by
    positivity

  have hLeftNonneg :
      0 ≤ h3RawProductConvolutionSecondMomentLeftMajorant F G ξ := by
    unfold h3RawProductConvolutionSecondMomentLeftMajorant
    exact integral_nonneg fun η => by positivity

  have hRightNonneg :
      0 ≤ h3RawProductConvolutionSecondMomentRightMajorant F G ξ := by
    unfold h3RawProductConvolutionSecondMomentRightMajorant
    exact integral_nonneg fun η => by positivity

  have hMajorNonneg :
      0 ≤ h3RawProductConvolutionSecondMomentMajorant F G ξ := by
    unfold h3RawProductConvolutionSecondMomentMajorant
    positivity

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Selected positive-time specialization: every pair of velocity coordinates
has an exact raw product convolution with an integrable second Fourier moment. -/
theorem h3RawProductConvolution_selectedRestart_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i j : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3RawProductConvolution (W t i) (W t j) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  apply h3RawProductConvolution_secondMoment_integrable_of

  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  · exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMoment_integrable
        hν U₀ hA hU₀ ht htR j

end
end Euclidean
end Bridge
end PrimeTensor
