import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelRawThirdMoment
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryQuotient

/-!
# Classicalization: first-Fréchet old-history right quotient

The scalar selected old-history quotient is already closed at the raw Fourier
level.  To differentiate one spatial coordinate as well, multiply that raw
quotient by the fixed Fourier derivative symbol

    d_a(ξ) = 2π i ξ_a.

Pointwise convergence is immediate from the scalar quotient theorem.  The only
new analytic input is domination.  The scalar quotient is bounded by the
zero-time heat generator, which costs two powers of `|ξ|`; the coordinate
symbol costs one more.  Therefore

    |d_a Q_h|
      ≤ ν (2π)^3 |ξ|^3 |A_t(ξ)|.

`SelectedDuhamelRawThirdMoment` supplies exactly this cubic integrability.

Dominated convergence then passes the coordinate quotient through inverse
Fourier reconstruction.  The resulting limit is the inverse Fourier transform
of the coordinate-multiplied zero-time heat generator.

This file deliberately stops at the Fourier reconstruction.  The next bridge
identifies these two inverse-Fourier objects with the literal coordinate
Fréchet difference quotient and the viscosity-weighted third spatial trace.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetHistoryQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw old-history right quotient after one fixed spatial coordinate
derivative multiplier. -/
noncomputable def h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i ξ

/-- Coordinate multiplier applied to the zero-time old-history heat
generator. -/
noncomputable def h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
      ν A t 0 hν U₀ hA hU₀ ht i ξ

/-- Frequencywise, the coordinate old-history quotient converges from the
right to the coordinate zero-time heat generator. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i a ξ)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a ξ)) := by
  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_zero_right
      hν U₀ hA hU₀ ht i ξ

  unfold
    h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
    h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude

  exact tendsto_const_nhds.mul hQ

/-- The coordinate old-history quotient is strongly measurable for every
positive increment. -/
theorem h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_aestronglyMeasurable_of_pos
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
  exact
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      (h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_aestronglyMeasurable_of_pos
        hν U₀ hA hU₀ ht hh i)

/-- The extra coordinate multiplier upgrades the scalar second-moment
majorant to the cubic selected-Duhamel moment. -/
theorem norm_h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_le_thirdMoment
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a ξ‖
      ≤
    (ν * (2 * Real.pi) ^ 3) *
      (‖ξ‖ ^ 3 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  have hSymbol :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

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

  unfold h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
  rw [norm_mul]

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ‖
        ≤
      h3FourierGradientMagnitude ξ *
        ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ‖ := by
            exact
              mul_le_mul_of_nonneg_right
                hSymbol
                (norm_nonneg _)
    _ ≤
      h3FourierGradientMagnitude ξ *
        ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i ξ‖ := by
            exact
              mul_le_mul_of_nonneg_left
                hQ
                (by
                  unfold h3FourierGradientMagnitude
                  positivity)
    _ =
      (ν * (2 * Real.pi) ^ 3) *
        (‖ξ‖ ^ 3 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
            rw [hGen]
            unfold h3FourierGradientMagnitude
            ring

/-- The coordinate-multiplied zero-time heat generator is integrable. -/
theorem h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    Integrable
      (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_thirdMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hGenInt :=
    h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_zero_integrable
      hν U₀ hA hU₀ ht htR i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        hGenInt.aestronglyMeasurable

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 3) *
            (‖ξ‖ ^ 3 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 3)

  refine hScaled.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun ξ => by
    unfold h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
    rw [norm_mul]

    have hSymbol :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

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
          ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
            ν A t 0 hν U₀ hA hU₀ ht i ξ‖
          ≤
        h3FourierGradientMagnitude ξ *
          ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
            ν A t 0 hν U₀ hA hU₀ ht i ξ‖ := by
              exact
                mul_le_mul_of_nonneg_right
                  hSymbol
                  (norm_nonneg _)
      _ =
        (ν * (2 * Real.pi) ^ 3) *
          (‖ξ‖ ^ 3 *
            ‖h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ‖) := by
              rw [hGen]
              unfold h3FourierGradientMagnitude
              ring

/-- Inverse-Fourier reconstruction of the coordinate old-history quotient. -/
noncomputable def h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i a)

/-- Inverse-Fourier reconstruction of the coordinate zero-time heat
generator. -/
noncomputable def h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a)

/-- The reconstructed coordinate old-history quotient converges pointwise in
space from the right to the reconstructed coordinate heat generator. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a x)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i a x)) := by
  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let Q : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ =>
      h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i a ξ

  let G : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ => phase ξ * Q h ξ

  let F0 : H3FourierPoint3 → ℂ :=
    fun ξ => phase ξ * G ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      (ν * (2 * Real.pi) ^ 3) *
        (‖ξ‖ ^ 3 *
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
        (h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_aestronglyMeasurable_of_pos
          hν U₀ hA hU₀ ht hh i a)

  have hBound :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F h ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ξ
    have hQ :=
      norm_h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_le_thirdMoment
        hν U₀ hA hU₀ ht hh i a ξ
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
      h3SelectedDuhamelRawFourierAmplitude_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i
    dsimp only [bound]
    exact hMoment.const_mul (ν * (2 * Real.pi) ^ 3)

  have hLim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun h : ℝ => F h ξ)
          (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 (F0 ξ)) := by
    filter_upwards with ξ
    have hQ :=
      tendsto_h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude_zero_right
        hν U₀ hA hU₀ ht i a ξ
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
        h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a x) := by
    funext h
    dsimp only [F, Q, phase]
    unfold h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F0 ξ)
        =
      h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
        ν A t hν U₀ hA hU₀ ht i a x := by
    dsimp only [F0, G, phase]
    unfold h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hGeneratorEq] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
