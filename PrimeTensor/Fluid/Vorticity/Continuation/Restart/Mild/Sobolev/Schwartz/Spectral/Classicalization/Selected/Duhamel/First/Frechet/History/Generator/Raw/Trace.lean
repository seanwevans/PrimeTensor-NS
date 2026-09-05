import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Raw.Third.Moment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.History.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Laplacian

/-!
# Classicalization: first-Fréchet old-history generator raw trace

The first-Fréchet old-history quotient now converges to the inverse Fourier
reconstruction of

    d_a(ξ) * G_t(ξ),

where `G_t` is the zero-time old-history heat-generator amplitude of the
complete selected Duhamel field.

At zero elapsed heat time,

    G_t(ξ) = -ν q(ξ) A_t(ξ),

with `A_t` the explicit selected Duhamel raw amplitude.  The already-compiled
coordinate-symbol trace identity

    Σ_k d_k(ξ) d_k(ξ) = -q(ξ)

therefore gives the exact raw identity

    d_a G_t
      =
    ν Σ_k d_a d_k d_k A_t.

This file packages the three ordered third-coordinate raw amplitudes, proves
their cubic-moment integrability, and records that exact trace identity.

No new PDE estimate is introduced; the only analytic input is the selected
Duhamel cubic raw moment already transported to the named amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetHistoryGeneratorRawTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- One ordered third-coordinate multiplier of the explicit selected Duhamel
raw Fourier amplitude. -/
noncomputable def h3SelectedDuhamelThirdCoordinateRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a k l : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol k ξ *
      (h3FourierDerivativeSymbol l ξ *
        h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ))

/-- Three coordinate symbols cost at most the radial cubic selected-Duhamel
moment. -/
theorem norm_h3SelectedDuhamelThirdCoordinateRawAmplitude_le_thirdMoment
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a k l : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelThirdCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a k l ξ‖
      ≤
    (2 * Real.pi) ^ 3 *
      (‖ξ‖ ^ 3 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  unfold h3SelectedDuhamelThirdCoordinateRawAmplitude
  rw [norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hk :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude k ξ
  have hl :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude l ξ

  have hN :
      0 ≤
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol k ξ‖ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hN))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol l ξ‖ *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hk
              (mul_nonneg (norm_nonneg _) hN))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hl hN)
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
    _ =
      (2 * Real.pi) ^ 3 *
        (‖ξ‖ ^ 3 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
        unfold h3FourierGradientMagnitude
        ring

/-- Every ordered third-coordinate multiplier of the named selected Duhamel
raw amplitude is integrable inside the restart radius. -/
theorem h3SelectedDuhamelThirdCoordinateRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a k l : Fin 3) :
    Integrable
      (h3SelectedDuhamelThirdCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a k l)
      (volume : Measure H3FourierPoint3) := by
  have hAmpInt :=
    h3SelectedDuhamelRawFourierAmplitude_integrable
      hν U₀ hA hU₀ ht i

  have hTargetMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelThirdCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a k l)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelThirdCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous k).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous l).aestronglyMeasurable.mul
            hAmpInt.aestronglyMeasurable))

  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_thirdMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 3 *
            (‖ξ‖ ^ 3 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul ((2 * Real.pi) ^ 3)

  refine hMajorant.mono' hTargetMeas ?_
  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SelectedDuhamelThirdCoordinateRawAmplitude_le_thirdMoment
      ν A t hν U₀ hA hU₀ ht i a k l ξ

/-- The coordinate-multiplied zero-time old-history heat generator is exactly
viscosity times the raw trace of the three selected Duhamel third-coordinate
multipliers. -/
theorem h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude_eq_viscosity_mul_thirdTrace
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a ξ
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        h3SelectedDuhamelThirdCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a k k ξ) := by
  unfold h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
  unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
  rw [
    h3SelectedDuhamelHistoryHeatRawAmplitude_zero
      hν U₀ hA hU₀ ht i
  ]
  unfold h3SelectedDuhamelThirdCoordinateRawAmplitude

  have hTrace :=
    sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare ξ

  have hCoeff :
      (((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))
        =
      (ν : ℂ) * (-(h3FourierGradientSquare ξ : ℂ)) := by
    push_cast
    ring

  rw [hCoeff]
  rw [← hTrace]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
