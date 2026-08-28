import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterVariationFubini

/-!
# Product integrability of the selected nine-quarter frozen endpoint term

The varying part of the selected terminal-half `9/4` Duhamel kernel is already
integrable on source-time × frequency.  This file packages the complementary
frozen terminal forcing in the same product-measure form.

For the frozen term we do not use the nonintegrable pointwise heat estimate
`(t-s)^(-9/8)`.  Instead, for each frequency we write

    |ξ|^(9/4) = |ξ|^(1/4) |ξ|^2

and integrate the second heat moment in source time first.  The existing frozen
second-moment primitive leaves the frequency weight `|ξ|^(1/4)`.  That weight
is controlled by

    |ξ|^(1/4) ≤ 1 + |ξ|,

so the already-closed Fourier `L¹` and first-moment bounds for the frozen
terminal forcing give the required outer frequency integrability.

Thus both pieces of the selected `9/4` terminal-half decomposition are now
honest product-space `L¹` kernels.  The next checkpoint can add them and push
the full weighted tail through the existing amplitude/Fubini/state pipeline.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedNineQuarterFrozenFubini
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A quarter Fourier weight is bounded by the sum of the zeroth and first
weights. -/
theorem norm_quarter_rpow_le_one_add_norm
    (ξ : H3FourierPoint3) :
    ‖ξ‖ ^ ((1 : ℝ) / 4) ≤ 1 + ‖ξ‖ := by
  by_cases hξ : ‖ξ‖ ≤ 1
  · calc
      ‖ξ‖ ^ ((1 : ℝ) / 4) ≤ 1 :=
        Real.rpow_le_one
          (norm_nonneg ξ)
          hξ
          (by norm_num)
      _ ≤ 1 + ‖ξ‖ := by
        linarith [norm_nonneg ξ]
  · have hξ1 : 1 ≤ ‖ξ‖ :=
      (lt_of_not_ge hξ).le
    calc
      ‖ξ‖ ^ ((1 : ℝ) / 4) ≤ ‖ξ‖ :=
        Real.rpow_le_self_of_one_le
          hξ1
          (by norm_num)
      _ ≤ 1 + ‖ξ‖ := by
        linarith

/-- The `9/4` radial weight splits as a quarter weight times the second
integer weight. -/
theorem h3FourierNineQuarterWeight_eq_quarter_mul_sq
    (ξ : H3FourierPoint3) :
    h3FourierNineQuarterWeight ξ
      =
    ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖ξ‖ ^ 2 := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  unfold h3FourierNineQuarterWeight

  calc
    ‖ξ‖ ^ ((9 : ℝ) / 4)
        =
      ‖ξ‖ ^ (((1 : ℝ) / 4) + 2) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖ξ‖ ^ (2 : ℝ) := by
        rw [
          Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (1 : ℝ) / 4)
            (by norm_num : 0 ≤ (2 : ℝ))
        ]
    _ =
      ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖ξ‖ ^ 2 := by
        exact
          congrArg
            (fun z : ℝ => ‖ξ‖ ^ ((1 : ℝ) / 4) * z)
            (Real.rpow_natCast ‖ξ‖ 2)

/-- The frozen selected forcing at the terminal time has an integrable quarter
Fourier moment.  This is an immediate consequence of its ordinary Fourier
`L¹` mass and already-closed first moment. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ‖ξ‖ ^ ((1 : ℝ) / 4) *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hN1 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖N ξ‖ + ‖ξ‖ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hN.norm.add hN1

  have hQuarterContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((1 : ℝ) / 4)) :=
    continuous_norm.rpow_const
      (fun _ => Or.inr (by norm_num : 0 ≤ (1 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hQuarterContinuous.aestronglyMeasurable.mul
      hN.norm.aestronglyMeasurable

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hQuarter0 :
      0 ≤ ‖ξ‖ ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (norm_nonneg ξ) _

  have hN0 : 0 ≤ ‖N ξ‖ := norm_nonneg _

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hQuarter0 hN0)
  ]

  calc
    ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖
        ≤
      (1 + ‖ξ‖) * ‖N ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_quarter_rpow_le_one_add_norm ξ)
          hN0
    _ = ‖N ξ‖ + ‖ξ‖ * ‖N ξ‖ := by
      ring

/-- Frozen terminal forcing after inserting the complex `9/4` Fourier weight. -/
noncomputable def h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
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
      h3RawFinLerayOuterProductDivergence
        (W t) (W t) i p.2)

/-- The frozen selected `9/4` terminal kernel is jointly strongly measurable
on the terminal-half product measure. -/
theorem h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_aestronglyMeasurable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
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

  unfold h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
  dsimp only [W]
  exact hWeight.mul hFrozen

/-- The frozen selected `9/4` terminal kernel is genuinely integrable on
source-time × frequency.  The proof integrates the already-closed second heat
moment in source time first, leaving only an integrable quarter Fourier moment
of the frozen forcing. -/
theorem h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let cInv : ℝ :=
    ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hhalf : t / 2 ≤ t := by
    linarith

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_aestronglyMeasurable
        hν U₀ hA hU₀ i

  have hQuarter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hQuarter.const_mul cInv

  refine (integrable_prod_iff' hJoint).2 ?_
  constructor

  · exact Filter.Eventually.of_forall fun ξ => by
      have hSecCont :
          Continuous
            (fun s : ℝ =>
              h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)) := by
        unfold h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
        dsimp only
        unfold h3HeatFourierSymbol
        fun_prop

      have hSecInterval :
          IntervalIntegrable
            (fun s : ℝ =>
              h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ))
            volume
            (t / 2)
            t :=
        hSecCont.intervalIntegrable (t / 2) t

      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hSecInterval
      dsimp only [μt]
      rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hSecInterval
      exact hSecInterval

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ∫ s : ℝ,
              ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)‖
              ∂μt)
          (volume : Measure H3FourierPoint3) :=
      hJoint.prod_swap.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_
    filter_upwards with ξ

    have hQuarter0 :
        0 ≤ ‖ξ‖ ^ ((1 : ℝ) / 4) :=
      Real.rpow_nonneg (norm_nonneg ξ) _

    have hWeight0 :
        0 ≤ h3FourierNineQuarterWeight ξ := by
      unfold h3FourierNineQuarterWeight
      positivity

    have hInnerEq :
        (∫ s : ℝ,
            ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt)
          =
        ‖ξ‖ ^ ((1 : ℝ) / 4) *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      rw [← integral_const_mul]
      dsimp only [μt]
      apply integral_congr_ae
      filter_upwards with s
      unfold h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
      dsimp only [N, W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hWeight0]
      rw [h3FourierNineQuarterWeight_eq_quarter_mul_sq]
      ring

    have hSecondBound :
        (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        cInv * ‖N ξ‖ := by
      dsimp only [cInv, N, W]
      exact
        h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_le
          hν U₀ hA hU₀ ht i ξ

    have hInnerNonneg :
        0 ≤
          ∫ s : ℝ,
            ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun s => norm_nonneg _)

    rw [Real.norm_eq_abs, abs_of_nonneg hInnerNonneg]
    rw [hInnerEq]

    calc
      ‖ξ‖ ^ ((1 : ℝ) / 4) *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        ‖ξ‖ ^ ((1 : ℝ) / 4) *
          (cInv * ‖N ξ‖) :=
            mul_le_mul_of_nonneg_left
              hSecondBound
              hQuarter0
      _ =
        cInv *
          (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) := by
            ring

end
end Euclidean
end Bridge
end PrimeTensor
