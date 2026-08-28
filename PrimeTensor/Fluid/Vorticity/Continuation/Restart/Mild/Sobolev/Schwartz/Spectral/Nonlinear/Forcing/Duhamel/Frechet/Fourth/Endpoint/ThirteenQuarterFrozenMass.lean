import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.SelectedForcingFiveQuarterMassBound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirteenQuarterFrozen

/-!
# Quantitative frozen thirteen-quarter endpoint

`ThirteenQuarterFrozen` already proves product-space integrability of the
terminal frozen source at the `13/4` Fourier weight.  Its proof uses

    |ξ|^(13/4) = |ξ|^(5/4) |ξ|²

and integrates the exact second heat moment in source time:

    ∫_{t/2}^t |ξ|² |H_{t-s}(ξ) N_t(ξ)| ds
      ≤
    (((2π)^2 ν)⁻¹) |N_t(ξ)|.

The remaining frequency density is exactly the terminal `5/4` forcing mass.
`SelectedForcingFiveQuarterMassBound` now bounds that mass numerically.

Therefore the complete frozen terminal-half contribution has the explicit
budget

    (((2π)^2 ν)⁻¹)
      * h3SelectedForcingFiveQuarterMassEnvelope ν A t.

This is stronger than the third-moment frozen estimate ultimately needed by
the full-third bootstrap.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirteenQuarterFrozenMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit quantitative budget for the selected frozen `13/4` terminal-half
contribution. -/
noncomputable def h3SelectedDuhamelTailThirteenQuarterFrozenBudget
    (ν A t : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    h3SelectedForcingFiveQuarterMassEnvelope ν A t

/-- Frequencywise source-time bound for the selected frozen `13/4` density. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenThirteenQuarterMoment_halfTail_timeIntegral_le_selectedEnvelopeDensity
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let N : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergence
        (W t) (W t) i
    (∫ s in (t / 2)..t,
        h3FourierThirteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let cInv : ℝ :=
    ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hFactor :
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

  have hSecond :
      (∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
        ≤
      cInv * ‖N ξ‖ := by
    dsimp only [cInv, N, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_timeIntegral_le
        hν U₀ hA hU₀ ht i ξ

  rw [hFactor]

  calc
    h3FourierFiveQuarterWeight ξ *
        (∫ s in (t / 2)..t,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
        ≤
      h3FourierFiveQuarterWeight ξ *
        (cInv * ‖N ξ‖) :=
      mul_le_mul_of_nonneg_left hSecond hFive0
    _ =
      cInv *
        (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
      ring
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
      rfl

/-- Quantitative frozen `13/4` endpoint budget after integrating source time
first and then frequency. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_frozenThirteenQuarterMoment_halfTail_iteratedNormIntegral_le
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
    let N : H3FourierPoint3 → ℂ :=
      h3RawFinLerayOuterProductDivergence
        (W t) (W t) i
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)
    (∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖(h3FourierThirteenQuarterWeight ξ *
              ‖h3HeatFourierSymbol ν (t - s) ξ‖) *
            ‖N ξ‖‖
          ∂μt)
      ≤
    h3SelectedDuhamelTailThirteenQuarterFrozenBudget ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let f : H3FourierPoint3 × ℝ → ℝ :=
    fun p =>
      (h3FourierThirteenQuarterWeight p.1 *
          ‖h3HeatFourierSymbol ν (t - p.2) p.1‖) *
        ‖N p.1‖

  let cInv : ℝ :=
    ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hProd :
      Integrable
        f
        ((volume : Measure H3FourierPoint3).prod μt) := by
    dsimp only [f, μt, N, W]
    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenThirteenQuarterMoment_halfTail_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hOuter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∫ s : ℝ, ‖f (ξ, s)‖ ∂μt)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((integrable_prod_iff hProd.aestronglyMeasurable).1 hProd).2

  have hN5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv *
            (h3FourierFiveQuarterWeight ξ * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hN5.const_mul cInv

  have hhalf : t / 2 ≤ t := by
    linarith

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        (∫ s : ℝ, ‖f (ξ, s)‖ ∂μt)
          ≤
        cInv *
          (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) := by
    intro ξ

    have hWeight0 :
        0 ≤ h3FourierThirteenQuarterWeight ξ := by
      unfold h3FourierThirteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hFive0 :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    have hInnerEq :
        (∫ s : ℝ, ‖f (ξ, s)‖ ∂μt)
          =
        ∫ s in (t / 2)..t,
          h3FourierThirteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖ := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      dsimp only [μt]
      apply integral_congr_ae
      filter_upwards with s

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

    rw [hInnerEq]

    dsimp only [cInv, N, W]

    exact
      h3RawFinLerayOuterProductDivergenceHeat_frozenThirteenQuarterMoment_halfTail_timeIntegral_le_selectedEnvelopeDensity
        hν U₀ hA hU₀ ht i ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖f (ξ, s)‖ ∂μt)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) :=
    integral_mono hOuter hMajor hPoint

  have hForce :
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i
        ≤
      h3SelectedForcingFiveQuarterMassEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMass_le_selectedEnvelope
        hν U₀ hA hU₀ ht htR i

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    positivity

  unfold h3SelectedDuhamelTailThirteenQuarterFrozenBudget

  calc
    (∫ ξ : H3FourierPoint3,
        ∫ s : ℝ, ‖f (ξ, s)‖ ∂μt)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          (h3FourierFiveQuarterWeight ξ * ‖N ξ‖) :=
      hIntegral
    _ =
      cInv *
        ∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖N ξ‖ := by
      rw [integral_const_mul]
    _ =
      cInv *
        h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i := by
      rfl
    _ ≤
      cInv *
        h3SelectedForcingFiveQuarterMassEnvelope ν A t :=
      mul_le_mul_of_nonneg_left hForce hcInv0
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        h3SelectedForcingFiveQuarterMassEnvelope ν A t := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
