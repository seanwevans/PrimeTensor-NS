import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryGenerator
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Selected Duhamel old-history right quotient

The previous checkpoint packaged the complete selected Duhamel raw amplitude,
its old-history heat orbit, and the zero-time heat generator.

This file closes the one-sided difference quotient at the raw Fourier level
and then passes that quotient through ordinary inverse Fourier reconstruction.

For fixed positive base time `t`, define

    Q_h(ξ) = h⁻¹ • (m(h,ξ) A_t(ξ) - A_t(ξ)).

Pointwise convergence as `h ↓ 0` is exactly
`HasDerivAt.tendsto_slope_zero_right`.

For domination, the mean-value inequality on `[0,h]` bounds

    ‖m(h,ξ)A_t(ξ) - A_t(ξ)‖

by `h` times the zero-time generator density.  Cancelling `h` gives the
integrable second-moment majorant already packaged in `HistoryGenerator`.

Dominated convergence then proves that the inverse Fourier reconstruction of
`Q_h` tends pointwise in space to the inverse Fourier reconstruction of the
zero-time old-history generator.

The remaining next checkpoint is purely linear algebra of Fourier
reconstruction: identify this inverse-Fourier quotient with the normalized
difference of the old-history heat representatives themselves.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelHistoryQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier difference quotient of the selected Duhamel old-history heat
orbit. -/
noncomputable def h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h⁻¹ •
    (h3SelectedDuhamelHistoryHeatRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ
      -
    h3SelectedDuhamelHistoryHeatRawAmplitude
        ν A t 0 hν U₀ hA hU₀ ht i ξ)

/-- The old-history raw quotient converges frequencywise from the right to the
zero-time heat generator. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i ξ)) := by
  have hDeriv :=
    h3SelectedDuhamelHistoryHeatRawAmplitude_hasDerivAt_time
      (h := (0 : ℝ))
      hν U₀ hA hU₀ ht i ξ

  have hSlope := hDeriv.tendsto_slope_zero_right

  simpa only [
    zero_add,
    h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
  ] using hSlope

/-- The old-history heat raw amplitude is Fourier `L¹` at every nonnegative
elapsed heat time. -/
theorem h3SelectedDuhamelHistoryHeatRawAmplitude_integrable_of_nonneg
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 ≤ h)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelHistoryHeatRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i)
      (volume : Measure H3FourierPoint3) := by
  have hAmpInt :=
    h3SelectedDuhamelRawFourierAmplitude_integrable
      hν U₀ hA hU₀ ht i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelHistoryHeatRawAmplitude
    exact
      (continuous_h3HeatFourierSymbol ν h).aestronglyMeasurable.mul
        hAmpInt.aestronglyMeasurable

  refine hAmpInt.mono hMeas ?_
  filter_upwards with ξ
  unfold h3SelectedDuhamelHistoryHeatRawAmplitude
  rw [norm_mul]
  exact
    mul_le_of_le_one_left
      (norm_nonneg
        (h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ))
      (norm_h3HeatFourierSymbol_le_one hν.le hh ξ)

/-- The raw quotient is strongly measurable for every nonzero increment for
which both heat endpoints are Fourier `L¹`; in particular this applies to
every positive increment. -/
theorem h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_aestronglyMeasurable_of_pos
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i)
      (volume : Measure H3FourierPoint3) := by
  have hH :=
    (h3SelectedDuhamelHistoryHeatRawAmplitude_integrable_of_nonneg
      hν U₀ hA hU₀ ht hh.le i).aestronglyMeasurable

  have h0 :=
    (h3SelectedDuhamelHistoryHeatRawAmplitude_integrable_of_nonneg
      hν U₀ hA hU₀ ht (le_refl (0 : ℝ)) i).aestronglyMeasurable

  unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
  exact AEStronglyMeasurable.const_smul (hH.sub h0) h⁻¹

/-- The positive old-history difference quotient is pointwise dominated by the
norm of the zero-time generator. -/
theorem norm_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_le_generator_zero
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ‖
      ≤
    ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t 0 hν U₀ hA hU₀ ht i ξ‖ := by
  let f : ℝ → ℂ :=
    fun r =>
      h3SelectedDuhamelHistoryHeatRawAmplitude
        ν A t r hν U₀ hA hU₀ ht i ξ

  let f' : ℝ → ℂ :=
    fun r =>
      h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        ν A t r hν U₀ hA hU₀ ht i ξ

  let C : ℝ :=
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖)

  have hDeriv :
      ∀ r ∈ Set.Icc (0 : ℝ) h,
        HasDerivWithinAt
          f
          (f' r)
          (Set.Icc (0 : ℝ) h)
          r := by
    intro r hr
    exact
      (h3SelectedDuhamelHistoryHeatRawAmplitude_hasDerivAt_time
        (h := r)
        hν U₀ hA hU₀ ht i ξ).hasDerivWithinAt

  have hBound :
      ∀ r ∈ Set.Ico (0 : ℝ) h,
        ‖f' r‖ ≤ C := by
    intro r hr
    dsimp only [f', C]
    exact
      norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_le_zero
        hν U₀ hA hU₀ ht hr.1 i ξ

  have hIncrement :
      ‖f h - f 0‖ ≤ C * (h - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hDeriv
      hBound
      h
      ⟨hh.le, le_rfl⟩

  have hInvNonneg : 0 ≤ h⁻¹ := inv_nonneg.mpr hh.le

  have hQuotient :
      ‖h⁻¹ • (f h - f 0)‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
    calc
      h⁻¹ * ‖f h - f 0‖
          ≤ h⁻¹ * (C * (h - 0)) :=
        mul_le_mul_of_nonneg_left hIncrement hInvNonneg
      _ = C := by
        rw [sub_zero]
        calc
          h⁻¹ * (C * h) = (h⁻¹ * h) * C := by ring
          _ = C := by simp [ne_of_gt hh]

  have hGeneratorNorm :
      C =
        ‖h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
          ν A t 0 hν U₀ hA hU₀ ht i ξ‖ := by
    rw [
      norm_h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
        hν U₀ hA hU₀ ht i ξ
    ]
    rw [
      h3SelectedDuhamelHistoryHeatRawAmplitude_zero
        hν U₀ hA hU₀ ht i
    ]

  unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
  dsimp only [f] at hQuotient
  rw [← hGeneratorNorm]
  exact hQuotient

/-- Inverse-Fourier reconstruction of the old-history raw difference
quotient. -/
noncomputable def h3SelectedDuhamelHistoryHeatQuotientRepresentative
    (ν A t h : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
      ν A t h hν U₀ hA hU₀ ht i)

/-- The inverse-Fourier old-history quotient converges pointwise in space from
the right to the zero-time heat-generator representative. -/
theorem tendsto_h3SelectedDuhamelHistoryHeatQuotientRepresentative_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    Tendsto
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i x)
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i x)) := by
  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let Q : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ =>
      h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
        ν A t h hν U₀ hA hU₀ ht i ξ

  let G : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude
      ν A t 0 hν U₀ hA hU₀ ht i

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun h ξ => phase ξ * Q h ξ

  let F0 : H3FourierPoint3 → ℂ :=
    fun ξ => phase ξ * G ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ => ‖G ξ‖

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
        (h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_aestronglyMeasurable_of_pos
          hν U₀ hA hU₀ ht hh i)

  have hBound :
      ∀ᶠ h : ℝ in (𝓝[Set.Ioi (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F h ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards with ξ
    have hQ :=
      norm_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_le_generator_zero
        hν U₀ hA hU₀ ht hh i ξ
    dsimp only [F, bound, Q, G]
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
    have hGen :=
      h3SelectedDuhamelHistoryHeatTimeGeneratorRawAmplitude_zero_integrable
        hν U₀ hA hU₀ ht htR i
    dsimp only [bound, G]
    exact hGen.norm

  have hLim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun h : ℝ => F h ξ)
          (𝓝[Set.Ioi (0 : ℝ)] 0)
          (𝓝 (F0 ξ)) := by
    filter_upwards with ξ
    have hQ :=
      tendsto_h3SelectedDuhamelHistoryHeatQuotientRawAmplitude_zero_right
        hν U₀ hA hU₀ ht i ξ
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
        h3SelectedDuhamelHistoryHeatQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i x) := by
    funext h
    dsimp only [F, Q, phase]
    unfold h3SelectedDuhamelHistoryHeatQuotientRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F0 ξ)
        =
      h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
        ν A t hν U₀ hA hU₀ ht i x := by
    dsimp only [F0, G, phase]
    unfold h3SelectedDuhamelHistoryHeatTimeGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hGeneratorEq] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
