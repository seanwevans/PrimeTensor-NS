import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathSelectedRawForcingPhysicalL2First
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Second.Forcing.Mass

/-!
# Selected raw forcing second Fourier moment

The first physical derivative of the unprojected selected forcing is already
closed.  The next spatial derivative needs exactly two further Fourier facts:

* the raw outer-product divergence has an integrable quadratic radial moment;
* every ordered product of two coordinate derivative symbols times that raw
  divergence belongs to Fourier `L²`.

Both are already consequences of the selected positive-time cubic state
moments and the public radial `L²` theorem.  This file exports those missing
unprojected bridges without introducing a new estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators ENNReal NNReal FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathSelectedRawForcingSecondMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At every strict positive selected restart time, one unprojected raw
outer-product divergence coordinate has an integrable quadratic Fourier
moment. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_secondMoment_integrable
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
        ‖ξ‖ ^ 2 *
          ‖h3RawFinOuterProductDivergence (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hW3 :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR k

  have hConv3 :
      ∀ k j : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ 3 *
              ‖h3RawProductConvolution (W t k) (W t j) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k j
    exact
      h3RawProductConvolution_thirdMoment_integrable_of
        (W t k) (W t j) (hW3 k) (hW3 j)

  exact
    h3RawFinOuterProductDivergence_secondMoment_integrable_of_convolutionThird
      (W t) (W t) i (hConv3 i)

/-- Two ordered Fourier coordinate multipliers of one raw selected forcing
coordinate remain integrable. -/
theorem h3RawFinOuterProductDivergence_selectedRestart_secondCoordinate_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinOuterProductDivergence (W t) (W t) i ξ))
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinOuterProductDivergence (W t) (W t) i

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hNInt :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact h3RawFinOuterProductDivergence_integrable (W t) (W t) i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hSecond.const_mul ((2 * Real.pi) ^ 2)

  apply hMajor.mono'
  · exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          hNInt.aestronglyMeasurable)
  · filter_upwards with ξ

    rw [norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

    have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
      unfold h3FourierGradientMagnitude
      positivity

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖)
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ * ‖N ξ‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
            hGrad0
      _ =
        (2 * Real.pi) ^ 2 *
          (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- Every ordered pair of coordinate multipliers of the unprojected selected
raw forcing belongs to Fourier `L²`. -/
theorem h3SelectedRestartRawForcing_secondCoordinate_memLp2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    MemLp
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3RawFinOuterProductDivergence (W t) (W t) i ξ))
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
          ((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ)
        2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_radialWeight_memLp2
        2 hν U₀ hA hU₀ ht htR i

  have hInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ * N ξ))
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinOuterProductDivergence_selectedRestart_secondCoordinate_integrable
        hν U₀ hA hU₀ ht htR i a b

  refine
    hRadial.of_le_mul
      (c := (2 * Real.pi) ^ 2)
      hInt.aestronglyMeasurable
      ?_

  filter_upwards with ξ

  rw [norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

  have hGrad0 : 0 ≤ h3FourierGradientMagnitude ξ := by
    unfold h3FourierGradientMagnitude
    positivity

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ * ‖N ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
          hGrad0
    _ =
      (2 * Real.pi) ^ 2 *
        ‖((‖ξ‖ ^ 2 : ℝ) : ℂ) * N ξ‖ := by
      unfold h3FourierGradientMagnitude
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 2)]
      ring

end

end Euclidean
end Bridge
end PrimeTensor
