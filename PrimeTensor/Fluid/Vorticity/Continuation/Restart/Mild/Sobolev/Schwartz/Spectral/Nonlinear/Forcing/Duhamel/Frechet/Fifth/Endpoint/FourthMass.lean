import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FourthSection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationFubini

/-!
# Fifth Fréchet endpoint: subcritical full-fourth source mass

`FourthSection` proves the one-source estimate

    m₄(H_{t-s} N_s)
      ≤
    M₅(ν,t,s) m₁₁/₄(N_s),

where

    M₅(ν,t,s) = C₅(ν) (t-s)^(-5/8).

The terminal singularity is integrable.  Therefore any interval-uniform
`11/4` forcing bound

    m₁₁/₄(N_s) ≤ B,    s ∈ (a,t),

closes product-space integrability and gives the explicit source budget

    ∬ |ξ|^4 |H_{t-s} N_s| dξ ds
      ≤
    B · (8/3) C₅(ν) (t-a)^(3/8).

As in the earlier `15/4` source-mass checkpoint, `B` is deliberately kept
abstract here.  A following layer can instantiate it with an interval-uniform
selected forcing `11/4` envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFourthMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Selected Duhamel source kernel carrying the full radial fourth Fourier
weight. -/
noncomputable def h3SelectedDuhamelFourthComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  (((‖p.2‖ ^ 4 : ℝ) : ℂ)) *
    h3SelectedDuhamelTailComplexKernel
      ν A t hν U₀ hA hU₀ i p

/-- The selected full-fourth weighted source kernel is jointly strongly
measurable on any positive terminal interval. -/
theorem h3SelectedDuhamelFourthComplexKernel_aestronglyMeasurable
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelFourthComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let μ :=
    ((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
      (volume : Measure H3FourierPoint3)

  have hWeightReal :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          ‖p.2‖ ^ 4) :=
    (continuous_norm.comp continuous_snd).pow 4

  have hWeight :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          (((‖p.2‖ ^ 4 : ℝ) : ℂ)))
        μ :=
    (Complex.continuous_ofReal.comp hWeightReal).aestronglyMeasurable

  have hSource :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i)
        μ :=
    (measurable_h3SelectedDuhamelTailComplexKernel
      hν U₀ hA hU₀ i).aestronglyMeasurable

  unfold h3SelectedDuhamelFourthComplexKernel
  exact hWeight.mul hSource

/-- Every strict source-time frequency section of the selected full-fourth
kernel is integrable. -/
theorem h3SelectedDuhamelFourthComplexKernel_section_integrable
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
        h3SelectedDuhamelFourthComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  have hs0 :
      0 < s :=
    lt_trans ha hs.1

  have hsR :
      s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hτ :
      0 < t - s :=
    sub_pos.mpr hs.2

  have hN :
      Integrable N
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hN11 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierElevenQuarterWeight ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_elevenQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hWeighted :=
    h3HeatFourierSymbol_fourth_weighted_mul_integrable_of_elevenQuarter
      hν hτ N hN hN11

  simpa only [
    h3SelectedDuhamelFourthComplexKernel,
    h3SelectedDuhamelTailComplexKernel,
    N, W
  ] using hWeighted

/-- One strict source section of the selected full-fourth kernel is bounded by
the normalized `5/4` terminal majorant times the selected forcing `11/4`
mass. -/
theorem h3SelectedDuhamelFourthComplexKernel_frequencyNormIntegral_le
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
        ‖h3SelectedDuhamelFourthComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)‖)
      ≤
    h3HeatFiveQuarterTerminalMajorant ν t s *
      h3RawFinLerayOuterProductDivergenceElevenQuarterMass
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
          ‖h3SelectedDuhamelFourthComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ

    have hWeight0 :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg (norm_nonneg ξ) 4

    unfold
      h3SelectedDuhamelFourthComplexKernel
      h3SelectedDuhamelTailComplexKernel

    dsimp only [N, W]

    rw [
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  have hSection :=
    h3SelectedForcingHeat_fourth_frequencyIntegral_le
      hν U₀ hA hU₀ ha hat htR hs i

  rw [hOuterEq]

  dsimp only [W, N] at hSection ⊢
  exact hSection

/-- Explicit source-time budget for a selected full-fourth Duhamel source whose
forcing `11/4` mass is uniformly bounded by `B` on `(a,t)`. -/
noncomputable def h3SelectedDuhamelFourthSourceBudget
    (ν a t B : ℝ) : ℝ :=
  B *
    (((8 : ℝ) / 3) *
      h3HeatFiveQuarterNormalizedCoefficient ν *
      (t - a) ^ ((3 : ℝ) / 8))

/-- Product-space integrability of the selected full-fourth source kernel under
a uniform forcing `11/4`-mass bound. -/
theorem h3SelectedDuhamelFourthComplexKernel_fubini_integrable_of_elevenQuarterMass_le
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
        h3RawFinLerayOuterProductDivergenceElevenQuarterMass
          (W s) (W s) i ≤ B) :
    Integrable
      (h3SelectedDuhamelFourthComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let M : ℝ → ℝ :=
    h3HeatFiveQuarterTerminalMajorant ν t

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelFourthComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelFourthComplexKernel_aestronglyMeasurable
      (a := a) (t := t) hν U₀ hA hU₀ i

  have hMajorInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact
      h3HeatFiveQuarterTerminalMajorant_intervalIntegrable

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
      h3SelectedDuhamelFourthComplexKernel_section_integrable
        hν U₀ hA hU₀ ha hat htR hs i

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun s : ℝ =>
            ∫ ξ : H3FourierPoint3,
              ‖h3SelectedDuhamelFourthComplexKernel
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
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceElevenQuarterMass
            (W s) (W s) i := by
      dsimp only [M, W]
      simpa using
        (h3SelectedDuhamelFourthComplexKernel_frequencyNormIntegral_le
          hν U₀ hA hU₀ ha hat htR hs i)

    have hM0 :
        0 ≤ M s := by
      dsimp only [M]
      unfold h3HeatFiveQuarterTerminalMajorant
      exact
        mul_nonneg
          (Real.rpow_nonneg
            (by positivity : 0 ≤ 3 * ν⁻¹)
            _)
          (Real.rpow_nonneg
            (sub_nonneg.mpr hs.2.le)
            _)

    have hMassBound :
        h3RawFinLerayOuterProductDivergenceElevenQuarterMass
            (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    have hBound :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
      calc
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
            ≤
          M s *
            h3RawFinLerayOuterProductDivergenceElevenQuarterMass
              (W s) (W s) i :=
          hSection
        _ ≤
          M s * B :=
          mul_le_mul_of_nonneg_left hMassBound hM0
        _ =
          B * M s := by
          ring

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
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

/-- Quantitative iterated norm budget for the selected full-fourth source
kernel under a uniform forcing `11/4`-mass bound. -/
theorem h3SelectedDuhamelFourthComplexKernel_iteratedNormIntegral_le_of_elevenQuarterMass_le
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
        h3RawFinLerayOuterProductDivergenceElevenQuarterMass
          (W s) (W s) i ≤ B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFourthComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelFourthSourceBudget ν a t B := by
  dsimp only

  let M : ℝ → ℝ :=
    h3HeatFiveQuarterTerminalMajorant ν t

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo a t)

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelFourthComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelFourthComplexKernel_aestronglyMeasurable
        (a := a) (t := t) hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelFourthComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelFourthComplexKernel_fubini_integrable_of_elevenQuarterMass_le
        hν U₀ hA hU₀ ha hat htR hB i hMassI

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        μt :=
    ((integrable_prod_iff hJoint).1 hProd).2

  have hMajorInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact
      h3HeatFiveQuarterTerminalMajorant_intervalIntegrable

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
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hSection :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceElevenQuarterMass
            (W s) (W s) i := by
      dsimp only [M, W]
      simpa using
        (h3SelectedDuhamelFourthComplexKernel_frequencyNormIntegral_le
          hν U₀ hA hU₀ ha hat htR hs i)

    have hM0 :
        0 ≤ M s := by
      dsimp only [M]
      unfold h3HeatFiveQuarterTerminalMajorant
      exact
        mul_nonneg
          (Real.rpow_nonneg
            (by positivity : 0 ≤ 3 * ν⁻¹)
            _)
          (Real.rpow_nonneg
            (sub_nonneg.mpr hs.2.le)
            _)

    have hMassBound :
        h3RawFinLerayOuterProductDivergenceElevenQuarterMass
            (W s) (W s) i
          ≤ B := by
      simpa only [W] using hMassI s hs

    calc
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFourthComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s *
          h3RawFinLerayOuterProductDivergenceElevenQuarterMass
            (W s) (W s) i :=
        hSection
      _ ≤
        M s * B :=
        mul_le_mul_of_nonneg_left hMassBound hM0
      _ =
        B * M s := by
        ring

  have hIntegral :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelFourthComplexKernel
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
      ((8 : ℝ) / 3) *
        h3HeatFiveQuarterNormalizedCoefficient ν *
        (t - a) ^ ((3 : ℝ) / 8) := by
    dsimp only [M]
    exact
      h3HeatFiveQuarterTerminalMajorant_integral_on hat.le

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFourthComplexKernel
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
        (((8 : ℝ) / 3) *
          h3HeatFiveQuarterNormalizedCoefficient ν *
          (t - a) ^ ((3 : ℝ) / 8)) := by
      rw [hExact]
    _ =
      h3SelectedDuhamelFourthSourceBudget ν a t B := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
