import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingSecondMoment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Third.Forcing.Mass

/-!
# Selected raw forcing third Fourier moment

The order-two physical raw forcing closure leaves one final spectral rung.
At strict positive selected restart time, the existing sixth-endpoint forcing
mass argument already supplies cubic moment control of each derivative-
convolution term.  Summing those terms gives the same cubic moment for the
unprojected raw outer-product divergence.

This file exposes that fact and packages every ordered product of three Fourier
coordinate derivative symbols times the raw selected forcing in Fourier `L²`.
No new smoothing estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingThirdMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict positive selected restart time, one unprojected raw
outer-product divergence coordinate has an integrable cubic Fourier moment. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_thirdMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 3 *
          ‖h3RawFinOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hDeriv :
      ∀ j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3FourierDerivativeSymbol j ξ *
                h3RawProductConvolution (W t i) (W t j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro j
    dsimp only [W]
    exact
      h3FourierDerivative_mul_rawProductConvolution_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i j

  exact
    h3RawFinOuterProductDivergence_thirdMoment_integrable_of_derivatives
      (W t) (W t) i hDeriv

/-- Three ordered Fourier coordinate multipliers of one raw selected forcing
coordinate remain integrable. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinOuterProductDivergence (W t) (W t) i ξ)))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  have hThird :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hThird.const_mul ((2 * Real.pi) ^ 3)

  apply hMajor.mono'
  · exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
            hNInt.aestronglyMeasurable))
  · filter_upwards with ξ

    rw [norm_mul, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
    have hc :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

    have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
      unfold h3FourierGradientMagnitude
      positivity

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖))
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            hGrad0
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ * ‖N ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
              hGrad0)
            hGrad0
      _ =
        (2 * Real.pi) ^ 3 *
          (‖ξ‖ ^ 3 * ‖N ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- Every ordered triple of coordinate multipliers of the unprojected selected
raw forcing belongs to Fourier `L²`. -/
theorem h3SelectedRestartRawForcing_thirdCoordinate_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3RawFinOuterProductDivergence (W t) (W t) i ξ)))
      2
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  have hRadial :
      MemLp
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_radialWeight_memLp2
        3 hν U₀ hA hU₀ ht htR i

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ * N ξ)))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_thirdCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b c

  refine
    hRadial.of_le_mul
      (c := (2 * Real.pi) ^ 3)
      hInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol c ξ‖ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          hGrad0
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ * ‖N ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
            hGrad0)
          hGrad0
    _ =
      (2 * Real.pi) ^ 3 *
        ‖((‖ξ‖ ^ 3 : ℝ) : ℂ) * N ξ‖ := by
      unfold h3FourierGradientMagnitude
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]
      ring

end

end Euclidean
end Bridge
end PrimeTensor
