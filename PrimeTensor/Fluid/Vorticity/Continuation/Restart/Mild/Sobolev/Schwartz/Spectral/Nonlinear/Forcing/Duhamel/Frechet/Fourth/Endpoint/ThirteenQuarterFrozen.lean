import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFiveQuarter
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Third.Endpoint.Frozen

/-!
# Frozen terminal contribution at the thirteen-quarter endpoint

The selected unheated nonlinear forcing now has an integrable `5/4` raw
Fourier moment at every positive restart time.

For the next fractional Duhamel endpoint, the frozen terminal contribution can
therefore be pushed from the old third spatial moment to `13/4`.

The key bookkeeping identity is

    |ξ|^(13/4) = |ξ|^(5/4) |ξ|^2.

The exact second heat primitive integrates the `|ξ|^2` factor in source time
with a viscosity-only coefficient.  The remaining frequency factor is exactly
the newly closed `5/4` moment of the frozen terminal forcing.

No terminal Hölder cancellation is needed for this frozen piece.  The varying
source-state contribution remains a separate endpoint problem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirteenQuarterFrozenEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The radial `13/4` Fourier weight. -/
noncomputable def h3FourierThirteenQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((13 : ℝ) / 4)

/-- The `13/4` weight factors as the new `5/4` forcing weight times the exact
second heat moment. -/
theorem h3FourierThirteenQuarterWeight_eq_fiveQuarter_mul_sq
    (ξ : H3FourierPoint3) :
    h3FourierThirteenQuarterWeight ξ
      =
    h3FourierFiveQuarterWeight ξ * ‖ξ‖ ^ 2 := by
  have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ

  unfold h3FourierThirteenQuarterWeight
  unfold h3FourierFiveQuarterWeight

  calc
    ‖ξ‖ ^ ((13 : ℝ) / 4)
        =
      ‖ξ‖ ^ (((5 : ℝ) / 4) + 2) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ ((5 : ℝ) / 4) * ‖ξ‖ ^ (2 : ℝ) := by
        rw [
          Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (5 : ℝ) / 4)
            (by norm_num : 0 ≤ (2 : ℝ))
        ]
    _ =
      ‖ξ‖ ^ ((5 : ℝ) / 4) * ‖ξ‖ ^ 2 := by
        exact
          congrArg
            (fun z : ℝ => ‖ξ‖ ^ ((5 : ℝ) / 4) * z)
            (Real.rpow_natCast ‖ξ‖ 2)

/-- The frozen selected terminal forcing has an integrable `13/4` heat-smoothed
moment on the terminal half.  Source time is integrated first through the exact
second heat primitive, leaving precisely the `5/4` terminal forcing moment. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenThirteenQuarterMoment_halfTail_fubini_integrable
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
      (fun p : H3FourierPoint3 × ℝ =>
        (h3FourierThirteenQuarterWeight p.1 *
            ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i p.1‖)
      ((volume : Measure H3FourierPoint3).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence (W t) (W t) i

  let f : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (h3FourierThirteenQuarterWeight p.1 *
          ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
        ‖N p.1‖

  let cInv : ℝ := ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hhalf : t / 2 ≤ t := by
    linarith

  have hc : 0 < (2 * Real.pi) ^ 2 * ν := by
    positivity

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    exact inv_nonneg.mpr hc.le

  have hN :
      Integrable N (volume : Measure H3FourierPoint3) := by
    dsimp only [N]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hN5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hWeightContinuous :
      Continuous h3FourierThirteenQuarterWeight := by
    unfold h3FourierThirteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (13 : ℝ) / 4))


  have hJoint :
      AEStronglyMeasurable
        f
        ((volume : Measure H3FourierPoint3).prod
          ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
    have hHeatMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ =>
            h3FourierThirteenQuarterWeight p.1 *
              ‖h3HeatFourierSymbol ν (t - p.2) p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) := by
      unfold h3FourierThirteenQuarterWeight
      unfold h3HeatFourierSymbol
      fun_prop

    have hNMeas :
        AEStronglyMeasurable
          (fun p : H3FourierPoint3 × ℝ => ‖N p.1‖)
          ((volume : Measure H3FourierPoint3).prod
            ((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t))) :=
      hN.norm.aestronglyMeasurable.comp_fst

    dsimp only [f]
    exact hHeatMeas.mul hNMeas

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            (h3FourierFiveQuarterWeight ξ * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hN5.const_mul cInv

  refine (integrable_prod_iff hJoint).2 ?_
  constructor

  · exact Filter.Eventually.of_forall fun ξ => by
      have hSecCont :
          Continuous (fun s : ℝ => f (ξ, s)) := by
        dsimp only [f]
        unfold h3FourierThirteenQuarterWeight
        unfold h3HeatFourierSymbol
        fun_prop

      have hSecInterval :
          IntervalIntegrable
            (fun s : ℝ => f (ξ, s))
            volume
            (t / 2)
            t :=
        hSecCont.intervalIntegrable (t / 2) t

      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf] at hSecInterval
      rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hSecInterval
      exact hSecInterval

  · have hOuterMeas :
        AEStronglyMeasurable
          (fun ξ : H3FourierPoint3 =>
            ∫ s : ℝ, ‖f (ξ, s)‖
              ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          (volume : Measure H3FourierPoint3) :=
      hJoint.norm.integral_prod_right'

    refine hMajorantInt.mono' hOuterMeas ?_
    filter_upwards with ξ

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hInnerEq :
        (∫ s : ℝ, ‖f (ξ, s)‖
            ∂((volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)))
          =
        ∫ s in (t / 2)..t,
          h3FourierThirteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae
      filter_upwards with s

      have hWeight0 :
          0 ≤ h3FourierThirteenQuarterWeight ξ := by
        unfold h3FourierThirteenQuarterWeight
        exact Real.rpow_nonneg (norm_nonneg ξ) _

      have hf0 :
          0 ≤
            (h3FourierThirteenQuarterWeight ξ *
                ‖h3HeatFourierSymbol ν (t - s) ξ‖) *
              ‖N ξ‖ :=
        mul_nonneg
          (mul_nonneg hWeight0 (norm_nonneg _))
          (norm_nonneg _)

      dsimp only [f]
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      rw [norm_mul]
      ring

    have hThirteenEq :
        (∫ s in (t / 2)..t,
            h3FourierThirteenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          =
        h3FourierFiveQuarterWeight ξ *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
      calc
        (∫ s in (t / 2)..t,
            h3FourierThirteenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
            =
          ∫ s in (t / 2)..t,
            h3FourierFiveQuarterWeight ξ *
              (‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
              apply intervalIntegral.integral_congr
              intro s _hs
              rw [h3FourierThirteenQuarterWeight_eq_fiveQuarter_mul_sq]
              ring
        _ =
          h3FourierFiveQuarterWeight ξ *
            (∫ s in (t / 2)..t,
              ‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
              rw [intervalIntegral.integral_const_mul]

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

    have hThirteenBound :
        (∫ s in (t / 2)..t,
            h3FourierThirteenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        cInv *
          (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
      rw [hThirteenEq]
      calc
        h3FourierFiveQuarterWeight ξ *
            (∫ s in (t / 2)..t,
              ‖ξ‖ ^ 2 *
                ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
            ≤
          h3FourierFiveQuarterWeight ξ *
            (cInv * ‖N ξ‖) :=
          mul_le_mul_of_nonneg_left hSecondBound hFive0
        _ =
          cInv *
            (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
          ring

    have hInnerNonneg :
        0 ≤
          ∫ s in (t / 2)..t,
            h3FourierThirteenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      exact
        intervalIntegral.integral_nonneg hhalf
          (fun _ _ => by
            exact
              mul_nonneg
                (by
                  unfold h3FourierThirteenQuarterWeight
                  exact Real.rpow_nonneg (norm_nonneg ξ) _)
                (norm_nonneg _))

    rw [hInnerEq, Real.norm_eq_abs, abs_of_nonneg hInnerNonneg]
    exact hThirteenBound

end
end Euclidean
end Bridge
end PrimeTensor
