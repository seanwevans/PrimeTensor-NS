import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Raw.Fifth.Moment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryQuotient

/-!
# Classicalization: third-Fréchet old-history right quotient

The scalar selected old-history quotient is already closed at the raw Fourier
level.  For the order-three mixed spatial derivative we multiply that quotient
by three fixed coordinate symbols

    d_a(ξ) d_b(ξ) d_c(ξ).

The scalar quotient is dominated by the zero-time heat generator, which costs
two Fourier powers.  The three coordinate symbols cost three more, so the
complete order-three quotient is dominated by

    ν (2π)^5 |ξ|^5 |A_t(ξ)|.

`Selected.Duhamel.Raw.Fifth.Moment` supplies exactly this integrability.

This file proves frequencywise convergence, fifth-moment domination, and
passes the third-coordinate quotient through inverse Fourier reconstruction.
It deliberately stops before identifying that reconstruction with the literal
third spatial Fréchet quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetHistoryQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw old-history right quotient after three fixed spatial coordinate
multipliers. -/
noncomputable def h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      (h3FourierDerivativeSymbol c ξ *
        h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ))

/-- Three coordinate multipliers applied to the zero-time old-history heat
generator. -/
noncomputable def h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      (h3FourierDerivativeSymbol c ξ *
        h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i ξ))

/-- Frequencywise, the third-coordinate old-history quotient converges from
the right to the corresponding zero-time heat generator. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i a b c ξ)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c ξ)) := by
  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_zero_right
      hν U₀ hA hU₀ ht i ξ

  unfold
    h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
    h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude

  exact
    tendsto_const_nhds.mul
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.mul hQ))

/-- The third-coordinate old-history quotient is strongly measurable for
every positive increment. -/
theorem h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_aestronglyMeasurable_of_pos
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a b c : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a b c)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
  exact
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
          (h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_aestronglyMeasurable_of_pos
            hν U₀ hA hU₀ ht hh i)))

/-- Three coordinate multipliers upgrade the scalar second-moment quotient
majorant to the full fifth selected-Duhamel moment. -/
theorem norm_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_le_fifthMoment
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a b c : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a b c ξ‖
      ≤
    (ν * (2 * Real.pi) ^ 5) *
      (‖ξ‖ ^ 5 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

  have hQ :=
    norm_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_le_generator_zero
      hν U₀ hA hU₀ ht hh i ξ

  have hGen :
      ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i ξ‖
        =
      (ν * (2 * Real.pi) ^ 2) *
        (‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
    rw [
      norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        hν U₀ hA hU₀ ht i ξ
    ]
    rw [
      h3SelectedDuhamelHistoryHeatRawAmplitude_zero
        hν U₀ hA hU₀ ht i
    ]

  unfold h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
  rw [norm_mul, norm_mul, norm_mul]

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ‖))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
            (by
              unfold h3FourierGradientMagnitude
              positivity))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
              ν A t 0 hν U₀ hA hU₀ ht i ξ‖)) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              hQ
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (ν * (2 * Real.pi) ^ 5) *
        (‖ξ‖ ^ 5 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      rw [hGen]
      unfold h3FourierGradientMagnitude
      ring

/-- The three-coordinate-multiplied zero-time heat generator is integrable. -/
theorem h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3) :
    Integrable
      (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_fifthMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hGenInt :=
    h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_zero_integrable
      hν U₀ hA hU₀ ht htR i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
            hGenInt.aestronglyMeasurable))

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 5) *
            (‖ξ‖ ^ 5 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 5)

  refine hScaled.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun ξ => by
    unfold h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
    rw [norm_mul, norm_mul, norm_mul]

    have ha :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
    have hb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
    have hc :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ

    have hGen :
        ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
            ν A t 0 hν U₀ hA hU₀ ht i ξ‖
          =
        (ν * (2 * Real.pi) ^ 2) *
          (‖ξ‖ ^ 2 *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      rw [
        norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          hν U₀ hA hU₀ ht i ξ
      ]
      rw [
        h3SelectedDuhamelHistoryHeatRawAmplitude_zero
          hν U₀ hA hU₀ ht i
      ]

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
                ν A t 0 hν U₀ hA hU₀ ht i ξ‖))
          ≤
        h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol b ξ‖ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
                ν A t 0 hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_right
            ha
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol c ξ‖ *
              ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
                ν A t 0 hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hb
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ ≤
        h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
                ν A t 0 hν U₀ hA hU₀ ht i ξ‖)) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity)
      _ =
        (ν * (2 * Real.pi) ^ 5) *
          (‖ξ‖ ^ 5 *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖) := by
        rw [hGen]
        unfold h3FourierGradientMagnitude
        ring

/-- Inverse-Fourier reconstruction of the third-coordinate old-history
quotient. -/
noncomputable def h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i a b c)

/-- Inverse-Fourier reconstruction of the third-coordinate zero-time heat
generator. -/
noncomputable def h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRepresentative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b c)

/-- The reconstructed third-coordinate old-history quotient converges
pointwise in space from the right to the reconstructed third-coordinate heat
generator. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a b c x)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i a b c x)) := by
  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let Q : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ =>
      h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a b c ξ

  let G : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b c

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ => phase ξ * Q h ξ

  let F0 : H3FourierPoint3 → ℂ :=
    fun ξ => phase ξ * G ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      (ν * (2 * Real.pi) ^ 5) *
        (‖ξ‖ ^ 5 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖)

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hFMeas :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F h)
          (volume : Measure H3FourierPoint3) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [F]
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_aestronglyMeasurable_of_pos
          hν U₀ hA hU₀ ht hh i a b c)

  have hBound :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F h ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ξ
    have hQ :=
      norm_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_le_fifthMoment
        hν U₀ hA hU₀ ht hh i a b c ξ
    dsimp only [F, bound, Q]
    simpa only [
      phase,
      norm_mul,
      Complex.norm_exp,
      Complex.mul_re,
      Complex.ofReal_re,
      Complex.ofReal_im,
      Complex.I_re,
      Complex.I_im,
      mul_zero,
      zero_mul,
      sub_self,
      Real.exp_zero,
      one_mul
    ] using hQ

  have hBoundInt :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3SelectedDuhamelRawFourierAmplitude_fifthMoment_integrable
        hν U₀ hA hU₀ ht htR i
    dsimp only [bound]
    exact hMoment.const_mul (ν * (2 * Real.pi) ^ 5)

  have hLim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun h : ℝ => F h ξ)
          (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 (F0 ξ)) := by
    filter_upwards with ξ
    have hQ :=
      tendsto_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude_zero_right
        hν U₀ hA hU₀ ht i a b c ξ
    dsimp only [F, F0, Q, G]
    exact tendsto_const_nhds.mul hQ

  have hMain :
      Tendsto
        (fun h : ℝ =>
          ∫ ξ : H3FourierPoint3, F h ξ)
        (𝓝[Set.Ioi (0 : ℝ)] 0)
        (𝓝
          (∫ ξ : H3FourierPoint3, F0 ξ)) := by
    exact
      tendsto_integral_filter_of_dominated_convergence
        (μ := (volume : Measure H3FourierPoint3))
        (l := (𝓝[Set.Ioi (0 : ℝ)] 0))
        (F := F)
        (f := F0)
        (bound := bound)
        hFMeas
        hBound
        hBoundInt
        hLim

  have hPathEq :
      (fun h : ℝ =>
        ∫ ξ : H3FourierPoint3, F h ξ)
        =
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a b c x) := by
    funext h
    dsimp only [F, Q, phase]
    unfold h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F0 ξ)
        =
      h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRepresentative
        ν A t hν U₀ hA hU₀ ht i a b c x := by
    dsimp only [F0, G, phase]
    unfold h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hGeneratorEq] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
