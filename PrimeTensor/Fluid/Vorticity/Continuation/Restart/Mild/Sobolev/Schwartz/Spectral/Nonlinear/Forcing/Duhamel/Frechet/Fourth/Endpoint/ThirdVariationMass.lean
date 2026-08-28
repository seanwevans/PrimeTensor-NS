import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationFubini
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirteenQuarterFrozenMass

/-!
# Quantitative full-third terminal variation mass

`ThirdVariationFubini` already isolates the exact remaining hypothesis for the
varying source at the full-third endpoint: on a positive terminal interval
`(a,t)`, assume the selected forcing difference has a uniform `5/4` raw
Fourier mass bound

    mass₅(N_s - N_t) ≤ B.

The frequency-section estimate then gives

    ∫ |ξ|³ |H_{t-s}(ξ)(N_s-N_t)(ξ)| dξ
      ≤
    M₇(ν,t,s) B,

where

    M₇(ν,t,s)
      =
    C₇(ν) (t-s)^(-7/8).

`SevenQuarterMajorant` already computes the exact terminal primitive

    ∫_a^t M₇(ν,t,s) ds
      =
    8 C₇(ν) (t-a)^(1/8).

This file packages the corresponding quantitative product-space norm budget:

    ∬ ‖K_var³(s,ξ)‖ dξ ds
      ≤
    B * 8 C₇(ν) (t-a)^(1/8).

No new PDE estimate is introduced.  Once a concrete interval-uniform `B` is
supplied, the full-third varying-source contribution becomes a single scalar
substitution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdVariationMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit source-time budget for a full-third terminal variation whose
selected forcing-difference `5/4` mass is bounded by `B` on `(a,t)`. -/
noncomputable def h3SelectedDuhamelTailThirdVariationBudget
    (ν a t B : ℝ) : ℝ :=
  B *
    (8 *
      h3HeatSevenQuarterNormalizedCoefficient ν *
      (t - a) ^ ((1 : ℝ) / 8))

/-- Quantitative full-third variation budget under a uniform selected forcing
difference `5/4` mass bound. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_iteratedNormIntegral_le_of_fiveQuarterMass_le
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
        h3SelectedForcingDifferenceFiveQuarterMass
          ν A t hν U₀ hA hU₀ i s ≤ B) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailThirdVariationComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelTailThirdVariationBudget ν a t B := by
  dsimp only

  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo a t)

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailThirdVariationComplexKernel_aestronglyMeasurable
        (a := a) (t := t) hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_fiveQuarterMass_le
        hν U₀ hA hU₀ ha hat htR hB i hMassI

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        μt := by
    exact
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
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    let D : H3FourierPoint3 → ℂ :=
      fun ξ =>
        h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ

    have hOuterEq :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          =
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      unfold h3SelectedDuhamelTailThirdVariationComplexKernel
      dsimp only [D, W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3)]

    have hSectionBound :
        (∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
          ≤
        M s *
          h3SelectedForcingDifferenceFiveQuarterMass
            ν A t hν U₀ hA hU₀ i s := by
      dsimp only [M, D, W]
      simpa only [h3SelectedForcingDifferenceFiveQuarterMass] using
        (h3SelectedDuhamelTailThirdVariation_frequencyIntegral_le
          hν U₀ hA hU₀ ha hat htR hs i)

    have hM0 :
        0 ≤ M s := by
      dsimp only [M]
      exact
        h3HeatSevenQuarterTerminalMajorant_nonneg
          hν hs.2

    have hMassBound :
        h3SelectedForcingDifferenceFiveQuarterMass
            ν A t hν U₀ hA hU₀ i s
          ≤ B :=
      hMassI s hs

    rw [hOuterEq]

    calc
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
          ≤
        M s *
          h3SelectedForcingDifferenceFiveQuarterMass
            ν A t hν U₀ hA hU₀ i s :=
        hSectionBound
      _ ≤
        M s * B :=
        mul_le_mul_of_nonneg_left hMassBound hM0
      _ =
        B * M s := by
        ring

  have hIntegral :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
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

  unfold h3SelectedDuhamelTailThirdVariationBudget

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailThirdVariationComplexKernel
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

end
end Euclidean
end Bridge
end PrimeTensor
