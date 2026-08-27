import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Fubini
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Selected terminal-tail raw Fourier amplitude and second-moment bootstrap

The selected variable-state terminal-tail kernel is now genuinely integrable on
the restricted source-time/Fourier product space, and Fubini has produced the
frequency-outer second-moment budget.

This file turns that product-space information into an actual Fourier
amplitude.

For one velocity coordinate define

    Tᵢ(ξ) =
      ∫_{t/2}^t
        H_{t-s}(ξ) Nᵢ(W(s),W(s))(ξ) ds.

We also integrate the complex weighted kernel

    |ξ|² H_{t-s}(ξ) Nᵢ(W(s),W(s))(ξ)

before taking norms.  Product integrability makes this weighted amplitude an
honest Fourier `L¹` object.  Linearity of the Bochner integral identifies it
with `|ξ|² Tᵢ(ξ)`, so the raw selected tail amplitude has two integrable
Fourier moments:

    ∫ |ξ|² |Tᵢ(ξ)| dξ
      ≤ selected second-moment budget.

The source-time integral is written over `Ioo (t/2) t`; a final theorem records
its equality with the usual oriented interval integral.  This avoids endpoint
bookkeeping while retaining the exact bridge to the named spectral tail state
in the next checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailMomentAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complex-valued selected retarded terminal-tail kernel before applying any
Fourier moment weight. -/
noncomputable def h3SelectedDuhamelTailComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  h3HeatFourierSymbol ν (t - p.1) p.2 *
    h3RawFinLerayOuterProductDivergence
      (W p.1) (W p.1) i p.2

/-- The selected complex terminal-tail kernel is jointly measurable. -/
theorem measurable_h3SelectedDuhamelTailComplexKernel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Measurable
      (h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i) := by
  unfold h3SelectedDuhamelTailComplexKernel
  exact
    measurable_h3RawFinLerayOuterProductDivergenceHeat_selectedRestart_joint
      (t := t) hν U₀ hA hU₀ i

/-- Complex selected tail kernel after inserting the second Fourier-moment
weight before source-time integration. -/
noncomputable def h3SelectedDuhamelTailSecondMomentComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  (‖p.2‖ ^ 2 : ℂ) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- The complex second-moment kernel is jointly measurable. -/
theorem measurable_h3SelectedDuhamelTailSecondMomentComplexKernel
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    Measurable
      (h3SelectedDuhamelTailSecondMomentComplexKernel
        ν A t hν U₀ hA hU₀ i) := by
  have hWeightReal :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          ‖p.2‖ ^ 2) :=
    ((continuous_norm.comp continuous_snd).pow 2).measurable

  have hNormComplex :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          (‖p.2‖ : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_norm.comp continuous_snd)

  have hWeightComplex :
      Measurable
        (fun p : ℝ × H3FourierPoint3 =>
          (‖p.2‖ ^ 2 : ℂ)) :=
    (hNormComplex.pow 2).measurable

  exact
    hWeightComplex.mul
      (measurable_h3SelectedDuhamelTailComplexKernel
        hν U₀ hA hU₀ i)

/-- The scalar second-moment kernel is nonnegative pointwise. -/
theorem h3SelectedDuhamelTailSecondMomentKernel_nonneg
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) :
    0 ≤
      h3SelectedDuhamelTailSecondMomentKernel
        ν A t hν U₀ hA hU₀ i p := by
  unfold h3SelectedDuhamelTailSecondMomentKernel
  positivity

/-- Taking the norm of the complex weighted kernel gives exactly the previously
defined nonnegative scalar second-moment density. -/
theorem norm_h3SelectedDuhamelTailSecondMomentComplexKernel_eq
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) :
    ‖h3SelectedDuhamelTailSecondMomentComplexKernel
        ν A t hν U₀ hA hU₀ i p‖
      =
    h3SelectedDuhamelTailSecondMomentKernel
      ν A t hν U₀ hA hU₀ i p := by
  unfold
    h3SelectedDuhamelTailSecondMomentComplexKernel
    h3SelectedDuhamelTailComplexKernel
    h3SelectedDuhamelTailSecondMomentKernel

  rw [norm_mul, norm_pow]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (norm_nonneg p.2)]

/-- The complex weighted selected tail kernel is genuinely integrable on the
restricted source-time/Fourier product space. -/
theorem h3SelectedDuhamelTailSecondMomentComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailSecondMomentComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hScalar :=
    h3SelectedDuhamelTailSecondMomentKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  refine
    hScalar.mono'
      (measurable_h3SelectedDuhamelTailSecondMomentComplexKernel
        hν U₀ hA hU₀ i).aestronglyMeasurable
      ?_

  filter_upwards with p

  rw [
    norm_h3SelectedDuhamelTailSecondMomentComplexKernel_eq
      hν U₀ hA hU₀ i p
  ]

/-- The actual raw Fourier amplitude of the selected terminal-half Duhamel
tail. -/
noncomputable def h3SelectedDuhamelTailRawFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- Source-time integral of the complex second-moment weighted tail kernel. -/
noncomputable def h3SelectedDuhamelTailSecondMomentFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelTailSecondMomentComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- The weighted second-moment Fourier amplitude is genuinely `L¹` in
frequency. -/
theorem h3SelectedDuhamelTailSecondMomentFourierAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailSecondMomentFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelTailSecondMomentComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailSecondMomentFourierAmplitude
  exact hOuter

/-- Pulling the frequency weight through the source-time integral identifies
the weighted amplitude with `|ξ|²` times the actual raw tail amplitude. -/
theorem h3SelectedDuhamelTailSecondMomentFourierAmplitude_eq_weight_mul_raw
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailSecondMomentFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ
      =
    (‖ξ‖ ^ 2 : ℂ) *
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  unfold
    h3SelectedDuhamelTailSecondMomentFourierAmplitude
    h3SelectedDuhamelTailSecondMomentComplexKernel
    h3SelectedDuhamelTailRawFourierAmplitude

  change
    (∫ s in Set.Ioo (t / 2) t,
      (‖ξ‖ ^ 2 : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    (‖ξ‖ ^ 2 : ℂ) *
      ∫ s in Set.Ioo (t / 2) t,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)

  rw [integral_const_mul]

/-- The actual raw tail amplitude has an integrable second Fourier moment. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_secondMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hWeighted :=
    h3SelectedDuhamelTailSecondMomentFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hNorm := hWeighted.norm

  refine hNorm.congr ?_

  filter_upwards with ξ

  rw [
    h3SelectedDuhamelTailSecondMomentFourierAmplitude_eq_weight_mul_raw
      hν U₀ hA hU₀ i ξ,
    norm_mul,
    norm_pow,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg ξ)
  ]

/-- Quantitative second Fourier-moment budget for the actual raw terminal-tail
amplitude. -/
theorem integral_secondMoment_h3SelectedDuhamelTailRawFourierAmplitude_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  let K : ℝ × H3FourierPoint3 → ℝ :=
    h3SelectedDuhamelTailSecondMomentKernel
      ν A t hν U₀ hA hU₀ i

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailSecondMomentComplexKernel
      ν A t hν U₀ hA hU₀ i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ∫ s : ℝ,
        ‖K (s, ξ)‖
        ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))

  have hKInt :
      Integrable
        K
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) := by
    dsimp only [K]
    exact
      h3SelectedDuhamelTailSecondMomentKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hZInt :
      Integrable
        Z
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z]
    exact
      h3SelectedDuhamelTailSecondMomentComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hMInt :
      Integrable M (volume : Measure H3FourierPoint3) := by
    dsimp only [M]
    exact hKInt.integral_norm_prod_right

  have hWeightedInt :=
    h3SelectedDuhamelTailSecondMomentFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hWeightedNormInt := hWeightedInt.norm

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailSecondMomentFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖
          ≤
        M ξ := by
    intro ξ

    calc
      ‖h3SelectedDuhamelTailSecondMomentFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖
          =
        ‖∫ s : ℝ,
            Z (s, ξ)
            ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))‖ := by
              rfl
      _ ≤
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
          ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) :=
            norm_integral_le_integral_norm _
      _ =
        M ξ := by
          dsimp only [M]
          apply integral_congr_ae
          filter_upwards with s
          dsimp only [Z, K]
          rw [
            norm_h3SelectedDuhamelTailSecondMomentComplexKernel_eq
              hν U₀ hA hU₀ i (s, ξ),
            Real.norm_eq_abs,
            abs_of_nonneg
              (h3SelectedDuhamelTailSecondMomentKernel_nonneg
                hν U₀ hA hU₀ i (s, ξ))
          ]

  have hWeightedOuterLe :
      (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailSecondMomentFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ := by
    exact
      integral_mono
        hWeightedNormInt
        hMInt
        hPointwise

  have hhalf : t / 2 ≤ t := by
    linarith

  have hMIntegralEq :
      (∫ ξ : H3FourierPoint3, M ξ)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ

    dsimp only [M]

    calc
      (∫ s : ℝ,
          ‖K (s, ξ)‖
          ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          =
        ∫ s : ℝ,
          K (s, ξ)
          ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
            apply integral_congr_ae
            filter_upwards with s
            rw [
              Real.norm_eq_abs,
              abs_of_nonneg
                (by
                  dsimp only [K]
                  exact
                    h3SelectedDuhamelTailSecondMomentKernel_nonneg
                      hν U₀ hA hU₀ i (s, ξ))
            ]
      _ =
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) := by
              dsimp only [K]
              symm
              rw [intervalIntegral.integral_of_le hhalf]
              rw [← restrict_Ioo_eq_restrict_Ioc]

  have hBudget :=
    h3SelectedDuhamelTailSecondMomentKernel_frequencyTimeIntegral_le
      hν U₀ hA hU₀ ht htR i

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailSecondMomentFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖ := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [
            h3SelectedDuhamelTailSecondMomentFourierAmplitude_eq_weight_mul_raw
              hν U₀ hA hU₀ i ξ,
            norm_mul,
            norm_pow,
            Complex.norm_real,
            Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg ξ)
          ]
    _ ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
        hWeightedOuterLe
    _ =
      ∫ ξ : H3FourierPoint3,
        ∫ s in (t / 2)..t,
          h3SelectedDuhamelTailSecondMomentKernel
            ν A t hν U₀ hA hU₀ i (s, ξ) :=
        hMIntegralEq
    _ ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t :=
        hBudget

/-- The set-integral raw amplitude is exactly the usual oriented interval
integral on the terminal half. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_eq_intervalIntegral
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ
      =
    ∫ s in (t / 2)..t,
      h3SelectedDuhamelTailComplexKernel
        ν A t hν U₀ hA hU₀ i (s, ξ) := by
  unfold h3SelectedDuhamelTailRawFourierAmplitude

  have hhalf : t / 2 ≤ t := by
    linarith

  symm
  rw [intervalIntegral.integral_of_le hhalf]
  rw [← restrict_Ioo_eq_restrict_Ioc]

end
end Euclidean
end Bridge
end PrimeTensor
