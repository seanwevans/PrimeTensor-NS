import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Amplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.NineQuarterMajorant

/-!
# Product integrability of the selected nine-quarter endpoint variation

The third-endpoint branch has already proved, for every source time in a
positive terminal interval,

    ∫ |ξ|^(9/4) |H_{t-s}(ξ) (N_s(ξ) - N_t(ξ))| dξ
      ≤ C (t-s)^(-7/8),

with an interval-integrable scalar majorant.

The existing selected-tail moment architecture packages source-time integrals
through genuine product-space integrability before applying Fubini.  This file
provides exactly that bridge for the varying part of the `9/4` bootstrap.

No new endpoint estimate is introduced.  The work here is measure-theoretic:

* record integrability of a `9/4`-weighted positive-lag heat multiplier against
  any Fourier-L¹ amplitude;
* prove joint strong measurability of the selected varying terminal kernel;
* use the already-closed `-7/8` majorant to obtain integrability on
  `(t/2,t) × FourierSpace`.

The frozen terminal contribution remains separate.  Once it is packaged at
`9/4`, the two pieces can be added and pushed through the existing
`Amplitude → LocalFubini → named L² state` route.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedNineQuarterVariationFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The complex `9/4` weight times a positive-lag heat multiplier preserves
Fourier integrability when applied to an arbitrary Fourier-L¹ amplitude. -/
theorem h3HeatFourierSymbol_nineQuarter_weighted_mul_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (h3FourierNineQuarterWeight ξ : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ := h3HeatNineQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatNineQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hWeightContinuous :
      Continuous h3FourierNineQuarterWeight := by
    unfold h3FourierNineQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hWeightComplexContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          (h3FourierNineQuarterWeight ξ : ℂ)) :=
    Complex.continuous_ofReal.comp hWeightContinuous

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          (h3FourierNineQuarterWeight ξ : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) :=
    hWeightComplexContinuous.aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF.norm.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hPoint :=
    norm_h3HeatFourierSymbol_nineQuarter_le
      hν hτ ξ

  have hWeight0 :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    positivity

  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hWeight0, norm_mul]

  calc
    h3FourierNineQuarterWeight ξ *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      (h3FourierNineQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖) * ‖F ξ‖ := by
      ring
    _ ≤
      C * ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right
        hPoint
        (norm_nonneg _)

/-- The selected varying terminal source after inserting the complex `9/4`
Fourier weight. -/
noncomputable def h3SelectedDuhamelTailNineQuarterVariationComplexKernel
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
  (h3FourierNineQuarterWeight p.2 : ℂ) *
    (h3HeatFourierSymbol ν (t - p.1) p.2 *
      (h3RawFinLerayOuterProductDivergence
          (W p.1) (W p.1) i p.2 -
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i p.2))

/-- The selected `9/4` variation kernel is jointly strongly measurable on the
terminal-half product measure. -/
theorem h3SelectedDuhamelTailNineQuarterVariationComplexKernel_aestronglyMeasurable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelTailNineQuarterVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let μ :=
    ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
      (volume : Measure H3FourierPoint3)

  have hWeightReal :
      Continuous
        (fun p : ℝ × H3FourierPoint3 =>
          h3FourierNineQuarterWeight p.2) := by
    unfold h3FourierNineQuarterWeight
    exact
      (continuous_norm.comp continuous_snd).rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (9 : ℝ) / 4))

  have hWeight :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          (h3FourierNineQuarterWeight p.2 : ℂ))
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
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i
        =
      (fun p : ℝ × H3FourierPoint3 =>
        (h3FourierNineQuarterWeight p.2 : ℂ) *
          (h3SelectedDuhamelTailComplexKernel
              ν A t hν U₀ hA hU₀ i p -
            h3HeatFourierSymbol ν (t - p.1) p.2 *
              h3RawFinLerayOuterProductDivergence
                (W t) (W t) i p.2)) := by
    funext p
    unfold
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel
      h3SelectedDuhamelTailComplexKernel
    dsimp only [W]
    ring

  rw [hAlgebra]
  exact hWeight.mul (hVar.sub hFrozen)

/-- For each source time strictly inside the terminal half, the frequency
section of the selected `9/4` variation kernel is integrable. -/
theorem h3SelectedDuhamelTailNineQuarterVariationComplexKernel_section_integrable
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hs : s ∈ Set.Ioo (t / 2) t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
          (W s) (W s) i ξ -
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ

  have hDs :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W s) (W s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W s) (W s) i

  have hDt :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W t) (W t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W t) (W t) i

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDs.sub hDt

  have hτ : 0 < t - s :=
    sub_pos.mpr hs.2

  have hWeighted :=
    h3HeatFourierSymbol_nineQuarter_weighted_mul_integrable
      hν hτ D hD

  simpa only [
    h3SelectedDuhamelTailNineQuarterVariationComplexKernel,
    D,
    W
  ] using hWeighted

/-- The selected varying `9/4` terminal kernel is genuinely integrable on
source-time × frequency.  This is the Fubini bridge needed by the tail-amplitude
packaging layer. -/
theorem h3SelectedDuhamelTailNineQuarterVariationComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailNineQuarterVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let K : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (t / 2) t

  let M : ℝ → ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
      ν t K

  have hhalfPos : 0 < t / 2 := by
    linarith

  have hhalfLt : t / 2 < t := by
    linarith

  have hhalfLe : t / 2 ≤ t :=
    hhalfLt.le

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
          (volume : Measure H3FourierPoint3)) :=
    h3SelectedDuhamelTailNineQuarterVariationComplexKernel_aestronglyMeasurable
      (t := t) hν U₀ hA hU₀ i

  have hMajorInterval :
      IntervalIntegrable
        M
        volume
        (t / 2)
        t := by
    dsimp only [M, K]
    exact
      h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_intervalIntegrable_selectedRestart

  have hMajor :
      Integrable
        M
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalfLe] at hMajorInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hMajorInterval
    exact hMajorInterval

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel_section_integrable
        hν U₀ hA hU₀ ht hs i

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun s : ℝ =>
            ∫ ξ : H3FourierPoint3,
              ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)) :=
      hJoint.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_

    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs

    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

    have hWeight0 :
        ∀ ξ : H3FourierPoint3,
          0 ≤ h3FourierNineQuarterWeight ξ := by
      intro ξ
      unfold h3FourierNineQuarterWeight
      positivity

    have hOuterEq :
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          =
        ∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence
                  (W s) (W s) i ξ -
                h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ)‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      unfold h3SelectedDuhamelTailNineQuarterVariationComplexKernel
      dsimp only [W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hWeight0 ξ)]

    have hOuterNonneg :
        0 ≤
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ξ => norm_nonneg _)

    rw [Real.norm_eq_abs, abs_of_nonneg hOuterNonneg]
    rw [hOuterEq]

    dsimp only [M, K, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_majorant_selectedRestart
        hν U₀ hA hU₀ hhalfPos hhalfLt htR hs i

end
end Euclidean
end Bridge
end PrimeTensor
