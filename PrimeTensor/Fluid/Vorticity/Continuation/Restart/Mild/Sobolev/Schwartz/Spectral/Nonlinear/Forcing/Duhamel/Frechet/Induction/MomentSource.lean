import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentHeatLift
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationFubini

/-!
# Fréchet endpoint induction: generic source-time moment budgets

`MomentHeatLift` removes all named exponents from one positive-lag source
section.  This file removes the remaining repetition in source time.

For an arbitrary output exponent `p`, define the selected weighted Duhamel
source kernel

    K_p(s,ξ) = w_p(ξ) H_{t-s}(ξ) N_s(ξ).

The first two theorems below are completely abstract in the terminal majorant:
if

    ∫ ‖K_p(s,ξ)‖ dξ ≤ M(s) B

on `(a,t)`, with `M` interval-integrable, then `K_p` is product-integrable and

    ∫_a^t ∫ ‖K_p(s,ξ)‖ dξ ds
      ≤
    B ∫_a^t M(s) ds.

The remainder specializes this once to each of the two residual heat gains
used forever by the bootstrap:

    q -> q + 7/4,    ∫ M₇ = 8 C₇(ν) (t-a)^(1/8),
    q -> q + 5/4,    ∫ M₅ = (8/3) C₅(ν) (t-a)^(3/8).

Thus all future source/Fubini steps are parametrized by the incoming forcing
moment `q`; there are no named `15/4`, `19/4`, `23/4`, ... source masses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentSource
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Selected Duhamel source kernel carrying an arbitrary generic Fourier
moment weight `p`. -/
noncomputable def h3SelectedDuhamelMomentComplexKernel
    (p ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (z : ℝ × H3FourierPoint3) : ℂ :=
  ((h3FourierMomentWeight p z.2 : ℝ) : ℂ) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i z

/-- The generic weighted selected source kernel is jointly strongly measurable
for every nonnegative output exponent. -/
theorem h3SelectedDuhamelMomentComplexKernel_aestronglyMeasurable
    {p ν A a t : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelMomentComplexKernel
        p ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let μ :=
    ((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
      (volume : Measure H3FourierPoint3)

  have hWeightReal :
      Continuous
        (fun z : ℝ × H3FourierPoint3 =>
          h3FourierMomentWeight p z.2) := by
    unfold h3FourierMomentWeight
    exact
      (continuous_norm.comp continuous_snd).rpow_const
        (fun _ => Or.inr hp)

  have hWeight :
      AEStronglyMeasurable
        (fun z : ℝ × H3FourierPoint3 =>
          ((h3FourierMomentWeight p z.2 : ℝ) : ℂ))
        μ :=
    (Complex.continuous_ofReal.comp hWeightReal).aestronglyMeasurable

  have hSource :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i)
        μ :=
    (measurable_h3SelectedDuhamelTailComplexKernel
      hν U₀ hA hU₀ i).aestronglyMeasurable

  unfold h3SelectedDuhamelMomentComplexKernel
  exact hWeight.mul hSource

/-- Abstract source-time Fubini closure.  Once each frequency section is
integrable and its norm integral is bounded by `M(s) * B`, an integrable
terminal majorant `M` closes product-space integrability. -/
theorem h3SelectedDuhamelMomentComplexKernel_fubini_integrable_of_section_bound
    {p ν A a t B : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (M : ℝ → ℝ)
    (hMInterval : IntervalIntegrable M volume a t)
    (hM0 : ∀ s ∈ Set.Ioo a t, 0 ≤ M s)
    (hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3))
    (hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B) :
    Integrable
      (h3SelectedDuhamelMomentComplexKernel
        p ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelMomentComplexKernel_aestronglyMeasurable
      (a := a) (t := t) hp hν U₀ hA hU₀ i

  have hMajorBase :
      Integrable
        M
        ((volume : Measure ℝ).restrict (Set.Ioo a t)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le] at hMInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hMInterval
    exact hMInterval

  have hMajor :
      Integrable
        (fun s : ℝ => B * M s)
        ((volume : Measure ℝ).restrict (Set.Ioo a t)) :=
    hMajorBase.const_mul B

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hSectionInt s hs

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun s : ℝ =>
            ∫ ξ : H3FourierPoint3,
              ‖h3SelectedDuhamelMomentComplexKernel
                p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ((volume : Measure ℝ).restrict (Set.Ioo a t)) :=
      hJoint.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_

    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    have hBound :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
      calc
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
            ≤
          M s * B :=
          hSectionLe s hs
        _ = B * M s := by
          ring

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ξ => norm_nonneg _)

    have hMajorNonneg :
        0 ≤ B * M s :=
      mul_nonneg hB (hM0 s hs)

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hOuterNonneg,
      abs_of_nonneg hMajorNonneg
    ] using hBound

/-- Abstract quantitative source-time budget corresponding to the previous
Fubini theorem. -/
theorem h3SelectedDuhamelMomentComplexKernel_iteratedNormIntegral_le_of_section_bound
    {p ν A a t B : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (M : ℝ → ℝ)
    (hMInterval : IntervalIntegrable M volume a t)
    (hM0 : ∀ s ∈ Set.Ioo a t, 0 ≤ M s)
    (hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3))
    (hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            p ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    B * ∫ s in a..t, M s := by
  dsimp only

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo a t)

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelMomentComplexKernel_aestronglyMeasurable
        (a := a) (t := t) hp hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelMomentComplexKernel
          p ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelMomentComplexKernel_fubini_integrable_of_section_bound
        hp hν U₀ hA hU₀ hat hB i
        M hMInterval hM0 hSectionInt hSectionLe

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        μt :=
    ((integrable_prod_iff hJoint).1 hProd).2

  have hMajorBase :
      Integrable M μt := by
    have hM := hMInterval
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le] at hM
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hM
    dsimp only [μt]
    exact hM

  have hMajor :
      Integrable
        (fun s : ℝ => B * M s)
        μt :=
    hMajorBase.const_mul B

  have hDom :
      ∀ᵐ s : ℝ ∂μt,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            p ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B :=
        hSectionLe s hs
      _ = B * M s := by
        ring

  have hIntegral :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              p ν A t hν U₀ hA hU₀ i (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      ∫ s : ℝ, B * M s ∂μt :=
    integral_mono_ae hOuter hMajor hDom

  have hMajorIntegralEq :
      (∫ s : ℝ, B * M s ∂μt)
        =
      B * ∫ s in a..t, M s := by
    rw [intervalIntegral.integral_of_le hat.le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    dsimp only [μt]
    rw [integral_const_mul]

  exact hIntegral.trans_eq hMajorIntegralEq

/-!
## Generic incoming forcing moment + residual seven-quarter heat gain
-/

/-- One strict selected source section gains `7/4` moments from an incoming
generic forcing moment `q`. -/
theorem h3SelectedDuhamel_addSevenQuarter_section_integrable_of_forcingMoment
    {q ν A t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i : Fin 3)
    (hNq :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelMomentComplexKernel
          (q + (7 : ℝ) / 4)
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact hNq

  let C : ℝ :=
    h3HeatSevenQuarterMomentCoefficient ν (t - s)

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((7 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierSevenQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_sevenQuarter_le
        hν hτ ξ)

  have hWeighted :=
    h3HeatFourierSymbol_momentLift_integrable
      hq
      (by norm_num : 0 ≤ (7 : ℝ) / 4)
      hC0 hHeat
      N hN hNq'

  simpa only [
    h3SelectedDuhamelMomentComplexKernel,
    h3SelectedDuhamelTailComplexKernel,
    N, W
  ] using hWeighted

/-- Quantitative selected `q -> q+7/4` source-section estimate. -/
theorem h3SelectedDuhamel_addSevenQuarter_frequencyNormIntegral_le
    {q ν A t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i : Fin 3)
    (hNq :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3)) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelMomentComplexKernel
          (q + (7 : ℝ) / 4)
          ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceMomentMass
        q (W s) (W s) i := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact hNq

  have hOuterEq :
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (7 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (7 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (q + (7 : ℝ) / 4) ξ :=
      h3FourierMomentWeight_nonneg _ ξ

    unfold
      h3SelectedDuhamelMomentComplexKernel
      h3SelectedDuhamelTailComplexKernel
    dsimp only [N, W]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hBase :=
    h3HeatFourierSymbol_addSevenQuarter_frequencyIntegral_le
      hq hν hs N hN hNq'

  rw [hOuterEq]

  unfold h3RawFinLerayOuterProductDivergenceMomentMass
  dsimp only [N, W] at hBase ⊢
  exact hBase

/-- Explicit generic source budget for the residual `7/4` heat lift. -/
noncomputable def h3SelectedDuhamelSevenQuarterSourceBudget
    (ν a t B : ℝ) : ℝ :=
  B *
    (8 *
      h3HeatSevenQuarterNormalizedCoefficient ν *
      (t - a) ^ ((1 : ℝ) / 8))

/-- Product-space closure of the generic `q -> q+7/4` selected source under a
uniform incoming forcing `q`-mass bound. -/
theorem h3SelectedDuhamel_addSevenQuarter_fubini_integrable_of_forcingMoment_le
    {q ν A a t B : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hForcingInt :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          (volume : Measure H3FourierPoint3))
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
          q (W s) (W s) i ≤ B) :
    Integrable
      (h3SelectedDuhamelMomentComplexKernel
        (q + (7 : ℝ) / 4)
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  have hp : 0 ≤ q + (7 : ℝ) / 4 := by
    linarith

  have hMInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact h3HeatSevenQuarterTerminalMajorant_intervalIntegrable

  have hM0 :
      ∀ s ∈ Set.Ioo a t, 0 ≤ M s := by
    intro s hs
    dsimp only [M]
    exact
      h3HeatSevenQuarterTerminalMajorant_nonneg
        hν hs.2

  have hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              (q + (7 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3) := by
    intro s hs
    exact
      h3SelectedDuhamel_addSevenQuarter_section_integrable_of_forcingMoment
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

  have hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              (q + (7 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B := by
    intro s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hBase :=
      h3SelectedDuhamel_addSevenQuarter_frequencyNormIntegral_le
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

    have hMass :
        h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hM0s : 0 ≤ M s :=
      hM0 s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (7 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i := by
        dsimp only [M, W]
        simpa using hBase
      _ ≤ M s * B :=
        mul_le_mul_of_nonneg_left hMass hM0s

  exact
    h3SelectedDuhamelMomentComplexKernel_fubini_integrable_of_section_bound
      hp hν U₀ hA hU₀ hat hB i
      M hMInterval hM0 hSectionInt hSectionLe

/-- Quantitative generic `q -> q+7/4` source-time budget. -/
theorem h3SelectedDuhamel_addSevenQuarter_iteratedNormIntegral_le_of_forcingMoment_le
    {q ν A a t B : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hForcingInt :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          (volume : Measure H3FourierPoint3))
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
          q (W s) (W s) i ≤ B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (7 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelSevenQuarterSourceBudget ν a t B := by
  dsimp only

  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  have hp : 0 ≤ q + (7 : ℝ) / 4 := by
    linarith

  have hMInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact h3HeatSevenQuarterTerminalMajorant_intervalIntegrable

  have hM0 :
      ∀ s ∈ Set.Ioo a t, 0 ≤ M s := by
    intro s hs
    dsimp only [M]
    exact
      h3HeatSevenQuarterTerminalMajorant_nonneg
        hν hs.2

  have hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              (q + (7 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3) := by
    intro s hs
    exact
      h3SelectedDuhamel_addSevenQuarter_section_integrable_of_forcingMoment
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

  have hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              (q + (7 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B := by
    intro s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hBase :=
      h3SelectedDuhamel_addSevenQuarter_frequencyNormIntegral_le
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

    have hMass :
        h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hM0s : 0 ≤ M s :=
      hM0 s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (7 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i := by
        dsimp only [M, W]
        simpa using hBase
      _ ≤ M s * B :=
        mul_le_mul_of_nonneg_left hMass hM0s

  have hBase :=
    h3SelectedDuhamelMomentComplexKernel_iteratedNormIntegral_le_of_section_bound
      hp hν U₀ hA hU₀ hat hB i
      M hMInterval hM0 hSectionInt hSectionLe

  have hExact :
      (∫ s in a..t, M s)
        =
      8 *
        h3HeatSevenQuarterNormalizedCoefficient ν *
        (t - a) ^ ((1 : ℝ) / 8) := by
    dsimp only [M]
    exact
      h3HeatSevenQuarterTerminalMajorant_integral_on hat.le

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (7 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂((volume : Measure ℝ).restrict (Set.Ioo a t)))
        ≤
      B * ∫ s in a..t, M s :=
      hBase
    _ =
      B *
        (8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - a) ^ ((1 : ℝ) / 8)) := by
      rw [hExact]
    _ =
      h3SelectedDuhamelSevenQuarterSourceBudget ν a t B := by
      rfl

/-!
## Generic incoming forcing moment + residual five-quarter heat gain
-/

/-- One strict selected source section gains `5/4` moments from an incoming
generic forcing moment `q`. -/
theorem h3SelectedDuhamel_addFiveQuarter_section_integrable_of_forcingMoment
    {q ν A t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i : Fin 3)
    (hNq :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelMomentComplexKernel
          (q + (5 : ℝ) / 4)
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hτ : 0 < t - s :=
    sub_pos.mpr hs

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact hNq

  let C : ℝ :=
    h3HeatFiveQuarterMomentCoefficient ν (t - s)

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatFiveQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((5 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierFiveQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_fiveQuarter_le
        hν hτ ξ)

  have hWeighted :=
    h3HeatFourierSymbol_momentLift_integrable
      hq
      (by norm_num : 0 ≤ (5 : ℝ) / 4)
      hC0 hHeat
      N hN hNq'

  simpa only [
    h3SelectedDuhamelMomentComplexKernel,
    h3SelectedDuhamelTailComplexKernel,
    N, W
  ] using hWeighted

/-- Quantitative selected `q -> q+5/4` source-section estimate. -/
theorem h3SelectedDuhamel_addFiveQuarter_frequencyNormIntegral_le
    {q ν A t s : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : s < t)
    (i : Fin 3)
    (hNq :
      let W : ℝ → H3SpectralFinVectorState :=
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3)) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelMomentComplexKernel
          (q + (5 : ℝ) / 4)
          ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceMomentMass
        q (W s) (W s) i := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact hNq

  have hOuterEq :
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (5 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (5 : ℝ) / 4) ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ

    have hWeight0 :
        0 ≤ h3FourierMomentWeight (q + (5 : ℝ) / 4) ξ :=
      h3FourierMomentWeight_nonneg _ ξ

    unfold
      h3SelectedDuhamelMomentComplexKernel
      h3SelectedDuhamelTailComplexKernel
    dsimp only [N, W]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hBase :=
    h3HeatFourierSymbol_addFiveQuarter_frequencyIntegral_le
      hq hν hs N hN hNq'

  rw [hOuterEq]

  unfold h3RawFinLerayOuterProductDivergenceMomentMass
  dsimp only [N, W] at hBase ⊢
  exact hBase

/-- Explicit generic source budget for the residual `5/4` heat lift. -/
noncomputable def h3SelectedDuhamelFiveQuarterSourceBudget
    (ν a t B : ℝ) : ℝ :=
  B *
    (((8 : ℝ) / 3) *
      h3HeatFiveQuarterNormalizedCoefficient ν *
      (t - a) ^ ((3 : ℝ) / 8))

/-- Product-space closure of the generic `q -> q+5/4` selected source under a
uniform incoming forcing `q`-mass bound. -/
theorem h3SelectedDuhamel_addFiveQuarter_fubini_integrable_of_forcingMoment_le
    {q ν A a t B : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hForcingInt :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          (volume : Measure H3FourierPoint3))
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
          q (W s) (W s) i ≤ B) :
    Integrable
      (h3SelectedDuhamelMomentComplexKernel
        (q + (5 : ℝ) / 4)
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let M : ℝ → ℝ :=
    h3HeatFiveQuarterTerminalMajorant ν t

  have hp : 0 ≤ q + (5 : ℝ) / 4 := by
    linarith

  have hMInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact h3HeatFiveQuarterTerminalMajorant_intervalIntegrable

  have hM0 :
      ∀ s ∈ Set.Ioo a t, 0 ≤ M s := by
    intro s hs
    dsimp only [M]
    unfold
      h3HeatFiveQuarterTerminalMajorant
      h3HeatFiveQuarterNormalizedCoefficient
    exact
      mul_nonneg
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)

  have hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              (q + (5 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3) := by
    intro s hs
    exact
      h3SelectedDuhamel_addFiveQuarter_section_integrable_of_forcingMoment
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

  have hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              (q + (5 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B := by
    intro s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hBase :=
      h3SelectedDuhamel_addFiveQuarter_frequencyNormIntegral_le
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

    have hMass :
        h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hM0s : 0 ≤ M s :=
      hM0 s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (5 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i := by
        dsimp only [M, W]
        simpa using hBase
      _ ≤ M s * B :=
        mul_le_mul_of_nonneg_left hMass hM0s

  exact
    h3SelectedDuhamelMomentComplexKernel_fubini_integrable_of_section_bound
      hp hν U₀ hA hU₀ hat hB i
      M hMInterval hM0 hSectionInt hSectionLe

/-- Quantitative generic `q -> q+5/4` source-time budget. -/
theorem h3SelectedDuhamel_addFiveQuarter_iteratedNormIntegral_le_of_forcingMoment_le
    {q ν A a t B : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hat : a < t)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hForcingInt :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierMomentWeight q ξ *
              ‖h3RawFinLerayOuterProductDivergence
                (W s) (W s) i ξ‖)
          (volume : Measure H3FourierPoint3))
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceMomentMass
          q (W s) (W s) i ≤ B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (5 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelFiveQuarterSourceBudget ν a t B := by
  dsimp only

  let M : ℝ → ℝ :=
    h3HeatFiveQuarterTerminalMajorant ν t

  have hp : 0 ≤ q + (5 : ℝ) / 4 := by
    linarith

  have hMInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact h3HeatFiveQuarterTerminalMajorant_intervalIntegrable

  have hM0 :
      ∀ s ∈ Set.Ioo a t, 0 ≤ M s := by
    intro s hs
    dsimp only [M]
    unfold
      h3HeatFiveQuarterTerminalMajorant
      h3HeatFiveQuarterNormalizedCoefficient
    exact
      mul_nonneg
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)

  have hSectionInt :
      ∀ s ∈ Set.Ioo a t,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3SelectedDuhamelMomentComplexKernel
              (q + (5 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ))
          (volume : Measure H3FourierPoint3) := by
    intro s hs
    exact
      h3SelectedDuhamel_addFiveQuarter_section_integrable_of_forcingMoment
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

  have hSectionLe :
      ∀ s ∈ Set.Ioo a t,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelMomentComplexKernel
              (q + (5 : ℝ) / 4)
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s * B := by
    intro s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hBase :=
      h3SelectedDuhamel_addFiveQuarter_frequencyNormIntegral_le
        hq hν U₀ hA hU₀ hs.2 i (hForcingInt s hs)

    have hMass :
        h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hM0s : 0 ≤ M s :=
      hM0 s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (5 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceMomentMass
            q (W s) (W s) i := by
        dsimp only [M, W]
        simpa using hBase
      _ ≤ M s * B :=
        mul_le_mul_of_nonneg_left hMass hM0s

  have hBase :=
    h3SelectedDuhamelMomentComplexKernel_iteratedNormIntegral_le_of_section_bound
      hp hν U₀ hA hU₀ hat hB i
      M hMInterval hM0 hSectionInt hSectionLe

  have hExact :
      (∫ s in a..t, M s)
        =
      ((8 : ℝ) / 3) *
        h3HeatFiveQuarterNormalizedCoefficient ν *
        (t - a) ^ ((3 : ℝ) / 8) := by
    dsimp only [M]
    exact
      h3HeatFiveQuarterTerminalMajorant_integral_on hat.le

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelMomentComplexKernel
            (q + (5 : ℝ) / 4)
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂((volume : Measure ℝ).restrict (Set.Ioo a t)))
        ≤
      B * ∫ s in a..t, M s :=
      hBase
    _ =
      B *
        (((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν *
          (t - a) ^ ((3 : ℝ) / 8)) := by
      rw [hExact]
    _ =
      h3SelectedDuhamelFiveQuarterSourceBudget ν a t B := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
