import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterSection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Fubini

/-!
# Fifth Fréchet endpoint: subcritical fifteen-quarter source mass

`FifteenQuarterSection` proves the one-source estimate

    m₁₅/₄(H_{t-s} N_s)
      ≤
    M₇(ν,t,s) m₂(N_s),

where

    M₇(ν,t,s) = C₇(ν) (t-s)^(-7/8).

The terminal singularity is integrable.  Therefore any interval-uniform
second-moment forcing bound

    m₂(N_s) ≤ B,    s ∈ (a,t),

closes product-space integrability and gives the explicit source budget

    ∬ |ξ|^(15/4) |H_{t-s} N_s| dξ ds
      ≤
    B · 8 C₇(ν) (t-a)^(1/8).

This checkpoint deliberately keeps `B` abstract.  The next layer can
instantiate it from the selected positive-time cubic state envelope without
mixing that scalar monotonicity bookkeeping into the Fubini argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Selected Duhamel source kernel carrying the radial `15/4` Fourier weight. -/
noncomputable def h3SelectedDuhamelFifteenQuarterComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  ((h3FourierFifteenQuarterWeight p.2 : ℝ) : ℂ) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- The selected weighted source kernel is jointly strongly measurable on any
positive terminal interval. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_aestronglyMeasurable
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelFifteenQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let μ :=
    ((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
      (volume : Measure H3FourierPoint3)

  have hWeightReal :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight p.2) := by
    unfold h3FourierFifteenQuarterWeight
    exact
      (continuous_norm.comp continuous_snd).rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (15 : ℝ) / 4))

  have hWeight :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          ((h3FourierFifteenQuarterWeight p.2 : ℝ) : ℂ))
        μ :=
    (Complex.continuous_ofReal.comp hWeightReal).aestronglyMeasurable

  have hSource :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i)
        μ :=
    (measurable_h3SelectedDuhamelTailComplexKernel
      hν U₀ hA hU₀ i).aestronglyMeasurable

  unfold h3SelectedDuhamelFifteenQuarterComplexKernel
  exact hWeight.mul hSource

/-- Every strict source-time frequency section of the selected `15/4` kernel is
integrable. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_section_integrable
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelFifteenQuarterComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hτ : 0 < t - s :=
    sub_pos.mpr hs.2

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hN2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hWeighted :=
    h3HeatFourierSymbol_fifteenQuarter_weighted_mul_integrable_of_second
      hν hτ N hN hN2

  simpa only [
    h3SelectedDuhamelFifteenQuarterComplexKernel,
    h3SelectedDuhamelTailComplexKernel,
    N, W
  ] using hWeighted

/-- One strict source section of the selected weighted kernel is bounded by the
normalized `7/4` terminal majorant times the selected forcing second mass. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_frequencyNormIntegral_le
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelFifteenQuarterComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceSecondMass
        (W s) (W s) i := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hOuterEq :
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFifteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ
    have hWeight0 :
        0 ≤ h3FourierFifteenQuarterWeight ξ := by
      unfold h3FourierFifteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _
    unfold
      h3SelectedDuhamelFifteenQuarterComplexKernel
      h3SelectedDuhamelTailComplexKernel
    dsimp only [N, W]
    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hSection :=
    h3SelectedForcingHeat_fifteenQuarter_frequencyIntegral_le
      hν U₀ hA hU₀ ha hat htR hs i

  rw [hOuterEq]

  dsimp only [W, N] at hSection ⊢
  exact hSection

/-- Explicit source-time budget for a selected `15/4` Duhamel source whose
forcing second mass is uniformly bounded by `B` on `(a,t)`. -/
noncomputable def h3SelectedDuhamelFifteenQuarterSourceBudget
    (ν a t B : ℝ) : ℝ :=
  B *
    (8 *
      h3HeatSevenQuarterNormalizedCoefficient ν *
      (t - a) ^ ((1 : ℝ) / 8))

/-- Product-space integrability of the selected `15/4` source kernel under a
uniform forcing second-mass bound. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_of_secondMass_le
    {ν A a t B : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W s) (W s) i ≤ B) :
    Integrable
      (h3SelectedDuhamelFifteenQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelFifteenQuarterComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelFifteenQuarterComplexKernel_aestronglyMeasurable
      (a := a) (t := t) hν U₀ hA hU₀ i

  have hMajorInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact
      h3HeatSevenQuarterTerminalMajorant_intervalIntegrable

  have hMajorBase :
      Integrable
        M
        ((volume : Measure ℝ).restrict (Set.Ioo a t)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le] at hMajorInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hMajorInterval
    exact hMajorInterval

  have hMajor :
      Integrable
        (fun s : ℝ => B * M s)
        ((volume : Measure ℝ).restrict (Set.Ioo a t)) :=
    hMajorBase.const_mul B

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_section_integrable
        hν U₀ hA hU₀ ha hat htR hs i

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun s : ℝ =>
            ∫ ξ : H3FourierPoint3,
              ‖h3SelectedDuhamelFifteenQuarterComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ((volume : Measure ℝ).restrict (Set.Ioo a t)) :=
      hJoint.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_

    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hSection :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceSecondMass
            (W s) (W s) i := by
      dsimp only [M, W]
      simpa using
        (h3SelectedDuhamelFifteenQuarterComplexKernel_frequencyNormIntegral_le
          hν U₀ hA hU₀ ha hat htR hs i)

    have hM0 :
        0 ≤ M s := by
      dsimp only [M]
      exact
        h3HeatSevenQuarterTerminalMajorant_nonneg
          hν hs.2

    have hMassBound :
        h3RawFinLerayOuterProductDivergenceSecondMass
            (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hBound :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
      calc
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
            ≤
          M s *
            h3RawFinLerayOuterProductDivergenceSecondMass
              (W s) (W s) i :=
          hSection
        _ ≤ M s * B :=
          mul_le_mul_of_nonneg_left hMassBound hM0
        _ = B * M s := by
          ring

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ξ => norm_nonneg _)

    have hMajorNonneg :
        0 ≤ B * M s :=
      mul_nonneg hB hM0

    simpa only [
      Real.norm_eq_abs,
      abs_of_nonneg hOuterNonneg,
      abs_of_nonneg hMajorNonneg
    ] using hBound

/-- Quantitative iterated norm budget for the selected `15/4` source kernel
under a uniform forcing second-mass bound. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_iteratedNormIntegral_le_of_secondMass_le
    {ν A a t B : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hB : 0 ≤ B)
    (i : Fin 3)
    (hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W s) (W s) i ≤ B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFifteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelFifteenQuarterSourceBudget ν a t B := by
  dsimp only

  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo a t)

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelFifteenQuarterComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_aestronglyMeasurable
        (a := a) (t := t) hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelFifteenQuarterComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_of_secondMass_le
        hν U₀ hA hU₀ ha hat htR hB i hMassI

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        μt :=
    ((integrable_prod_iff hJoint).1 hProd).2

  have hMajorInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact
      h3HeatSevenQuarterTerminalMajorant_intervalIntegrable

  have hMajorBase :
      Integrable M μt := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le] at hMajorInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hMajorInterval
    dsimp only [μt]
    exact hMajorInterval

  have hMajor :
      Integrable
        (fun s : ℝ => B * M s)
        μt :=
    hMajorBase.const_mul B

  have hDom :
      ∀ᵐ s : ℝ ∂μt,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hSection :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceSecondMass
            (W s) (W s) i := by
      dsimp only [M, W]
      simpa using
        (h3SelectedDuhamelFifteenQuarterComplexKernel_frequencyNormIntegral_le
          hν U₀ hA hU₀ ha hat htR hs i)

    have hM0 :
        0 ≤ M s := by
      dsimp only [M]
      exact
        h3HeatSevenQuarterTerminalMajorant_nonneg
          hν hs.2

    have hMassBound :
        h3RawFinLerayOuterProductDivergenceSecondMass
            (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFifteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceSecondMass
            (W s) (W s) i :=
        hSection
      _ ≤ M s * B :=
        mul_le_mul_of_nonneg_left hMassBound hM0
      _ = B * M s := by
        ring

  have hIntegral :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFifteenQuarterComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
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
          ‖h3SelectedDuhamelFifteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
        ≤
      ∫ s : ℝ, B * M s ∂μt :=
      hIntegral
    _ =
      B * ∫ s in a..t, M s :=
      hMajorIntegralEq
    _ =
      B *
        (8 *
          h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - a) ^ ((1 : ℝ) / 8)) := by
      rw [hExact]
    _ =
      h3SelectedDuhamelFifteenQuarterSourceBudget ν a t B := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
