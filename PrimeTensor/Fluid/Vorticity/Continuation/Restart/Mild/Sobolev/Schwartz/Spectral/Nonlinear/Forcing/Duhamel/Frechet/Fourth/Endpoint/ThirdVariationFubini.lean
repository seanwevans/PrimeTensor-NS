import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationSection
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterVariationFubini

/-!
# Full-third terminal variation: Fubini criterion

`ThirdVariationSection` closes the complete frequency analysis at a strict
terminal source time:

* the forcing difference carries an integrable `5/4` moment;
* the residual `7/4` heat multiplier supplies the remaining power in
  `3 = 5/4 + 7/4`;
* every frequency section is integrable;
* its full-third frequency integral is bounded by

      M₇(ν,t,s) · mass₅(s),

  where `M₇(ν,t,s) ~ (t-s)^(-7/8)`.

`SevenQuarterMajorant` proves that `M₇` is integrable in source time.

This file packages the exact remaining Fubini bridge.  If the selected
`5/4`-weighted forcing-difference mass is uniformly bounded by some finite
constant `B` on a positive terminal interval `(a,t)`, then the complete
full-third variation kernel is integrable on

    (a,t) × FourierSpace.

No existence theorem for `B` is assumed or hidden here.  Producing that
uniform positive-time bound is isolated as the sole remaining analytic input
for the variation half of the full-third endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdVariationFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The `5/4` weighted Fourier mass of the selected forcing difference between
source time `s` and terminal time `t`. -/
noncomputable def h3SelectedForcingDifferenceFiveQuarterMass
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (s : ℝ) : ℝ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  ∫ ξ : H3FourierPoint3,
    h3FourierFiveQuarterWeight ξ *
      ‖h3RawFinLerayOuterProductDivergence
          (W s) (W s) i ξ -
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ‖

/-- The selected `5/4` forcing-difference mass is nonnegative. -/
theorem h3SelectedForcingDifferenceFiveQuarterMass_nonneg
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (s : ℝ) :
    0 ≤
      h3SelectedForcingDifferenceFiveQuarterMass
        ν A t hν U₀ hA hU₀ i s := by
  unfold h3SelectedForcingDifferenceFiveQuarterMass
  dsimp only
  exact integral_nonneg fun ξ => by
    exact
      mul_nonneg
        (by
          unfold h3FourierFiveQuarterWeight
          exact Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

/-- The selected full-third variation kernel is jointly strongly measurable on
an arbitrary positive terminal interval. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_aestronglyMeasurable
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelTailThirdVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μ :=
    ((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
      (volume : Measure H3FourierPoint3)

  have hWeightReal :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          ‖p.2‖ ^ 3) :=
    (continuous_norm.comp continuous_snd).pow 3

  have hWeight :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          (((‖p.2‖ ^ 3 : ℝ) : ℂ)))
        μ :=
    (Complex.continuous_ofReal.comp hWeightReal).aestronglyMeasurable

  have hVar :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i)
        μ :=
    (measurable_h3SelectedDuhamelTailComplexKernel
      hν U₀ hA hU₀ i).aestronglyMeasurable

  have hHeatContinuous :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (t - p.1) p.2) := by
    unfold h3HeatFourierSymbol
    fun_prop

  have hN :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W t) (W t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W t) (W t) i

  have hFrozen :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          h3HeatFourierSymbol ν (t - p.1) p.2 *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i p.2)
        μ :=
    hHeatContinuous.aestronglyMeasurable.mul
      hN.aestronglyMeasurable.comp_snd

  have hAlgebra :
      h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i
        =
      (fun p : ℝ × H3FourierPoint3 =>
        (((‖p.2‖ ^ 3 : ℝ) : ℂ)) *
          (h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i p -
            h3HeatFourierSymbol ν (t - p.1) p.2 *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i p.2)) := by
    funext p
    unfold
      h3SelectedDuhamelTailThirdVariationComplexKernel
      h3SelectedDuhamelTailComplexKernel
    dsimp only [W]
    ring

  rw [hAlgebra]
  exact hWeight.mul (hVar.sub hFrozen)

/-- The normalized terminal `7/4` majorant is nonnegative at every strict
source time. -/
theorem h3HeatSevenQuarterTerminalMajorant_nonneg
    {ν t s : ℝ}
    (hν : 0 < ν)
    (hs : s < t) :
    0 ≤ h3HeatSevenQuarterTerminalMajorant ν t s := by
  unfold h3HeatSevenQuarterTerminalMajorant
  unfold h3HeatSevenQuarterNormalizedCoefficient
  have hbase : 0 ≤ 3 * ν⁻¹ := by
    positivity
  have hlag : 0 ≤ t - s := sub_nonneg.mpr hs.le
  exact
    mul_nonneg
      (Real.rpow_nonneg hbase _)
      (Real.rpow_nonneg hlag _)

/-- Fubini criterion for the selected full-third variation kernel.

A uniform `5/4` weighted forcing-difference mass bound on `(a,t)` is enough to
close product-space integrability because the remaining heat singularity is the
integrable kernel `(t-s)^(-7/8)`. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_fiveQuarterMass_le
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
    Integrable
      (h3SelectedDuhamelTailThirdVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let M : ℝ → ℝ :=
    h3HeatSevenQuarterTerminalMajorant ν t

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelTailThirdVariationComplexKernel_aestronglyMeasurable
      (a := a) (t := t) hν U₀ hA hU₀ i

  have hMajorInterval :
      IntervalIntegrable M volume a t := by
    dsimp only [M]
    exact h3HeatSevenQuarterTerminalMajorant_intervalIntegrable

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
      h3SelectedDuhamelTailThirdVariationComplexKernel_section_integrable
        hν U₀ hA hU₀ ha hat htR hs i

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun s : ℝ =>
            ∫ ξ : H3FourierPoint3,
              ‖h3SelectedDuhamelTailThirdVariationComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ((volume : Measure ℝ).restrict (Set.Ioo a t)) :=
      hJoint.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_

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
        h3HeatSevenQuarterTerminalMajorant ν t s *
          h3SelectedForcingDifferenceFiveQuarterMass
            ν A t hν U₀ hA hU₀ i s := by
      dsimp only [D, W]
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

    have hBound :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        B * M s := by
      rw [hOuterEq]
      calc
        (∫ ξ : H3FourierPoint3,
            ‖ξ‖ ^ 3 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
            ≤
          M s *
            h3SelectedForcingDifferenceFiveQuarterMass
              ν A t hν U₀ hA hU₀ i s := by
          simpa only [M] using hSectionBound
        _ ≤ M s * B :=
          mul_le_mul_of_nonneg_left hMassBound hM0
        _ = B * M s := by
          ring

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailThirdVariationComplexKernel
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

end
end Euclidean
end Bridge
end PrimeTensor
