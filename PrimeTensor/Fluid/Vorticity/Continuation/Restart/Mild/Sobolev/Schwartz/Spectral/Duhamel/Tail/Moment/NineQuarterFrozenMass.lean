import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.QuarterForcingMass

/-!
# Quantitative mass budget for the frozen selected nine-quarter tail

`NineQuarterFrozenFubini` already proves that the frozen terminal contribution

    |ξ|^(9/4) H_{t-s}(ξ) N_t(ξ)

is integrable on `(t/2,t) × FourierSpace`.

Its proof integrates the second heat moment in source time first, using

    |ξ|^(9/4) = |ξ|^(1/4) |ξ|²,

and obtains the pointwise frequency bound

    ∫_{t/2}^t |ξ|^(9/4) |H_{t-s}(ξ) N_t(ξ)| ds
      ≤
    (((2π)^2 ν)⁻¹) |ξ|^(1/4) |N_t(ξ)|.

`QuarterForcingMass` now gives a numerical bound for the remaining quarter
forcing mass.  This file packages the resulting iterated-norm estimate

    ∫_ξ ∫_{t/2}^t ‖K_frozen(s,ξ)‖ ds dξ
      ≤
    (((2π)^2 ν)⁻¹) B_{1/4}(ν,A,t).

This is exactly the scalar budget needed by the subsequent amplitude estimate,
where `norm_integral_le_integral_norm` converts the source-time integral into
the Fourier amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterFrozenMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit budget for the frozen selected `9/4` terminal-half contribution. -/
noncomputable def h3SelectedDuhamelTailNineQuarterFrozenBudget
    (ν A t : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    h3SelectedForcingQuarterMomentEnvelope ν A t

/-- For every frequency, the source-time norm integral of the frozen selected
`9/4` kernel is bounded by the second-heat primitive coefficient times the
quarter-weighted terminal forcing amplitude. -/
theorem h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_timeNormIntegral_le
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
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)
    (∫ s : ℝ,
        ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂μt)
      ≤
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) := by
  dsimp only

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
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) := by
      rfl

/-- Quantitative frozen `9/4` Fubini budget: the iterated integral of the
kernel norm is bounded by the second-heat primitive coefficient times the
selected quarter forcing envelope. -/
theorem h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_iteratedNormIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)
    (∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
          ∂μt)
      ≤
    h3SelectedDuhamelTailNineQuarterFrozenBudget ν A t := by
  dsimp only

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

  have hJoint :
      AEStronglyMeasurable
        (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_aestronglyMeasurable
        hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hOuter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∫ s : ℝ,
            ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt)
        (volume : Measure H3FourierPoint3) := by
    exact
      ((integrable_prod_iff' hJoint).1 hProd).2

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

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        (∫ s : ℝ,
            ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt)
          ≤
        cInv *
          (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) := by
    intro ξ
    dsimp only [cInv, μt, N, W]
    exact
      h3SelectedDuhamelTailNineQuarterFrozenComplexKernel_timeNormIntegral_le
        hν U₀ hA hU₀ ht i ξ

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ,
            ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) :=
    integral_mono hOuter hMajor hPoint

  have hQuarterBound :
      h3RawFinLerayOuterProductDivergenceQuarterMass
          (W t) (W t) i
        ≤
      h3SelectedForcingQuarterMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_quarterMass_le
        hν U₀ hA hU₀ ht htR i

  have hcInv0 : 0 ≤ cInv := by
    dsimp only [cInv]
    positivity

  unfold h3SelectedDuhamelTailNineQuarterFrozenBudget

  calc
    (∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖h3SelectedDuhamelTailNineQuarterFrozenComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
          ∂μt)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv *
          (‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖) :=
      hIntegral
    _ =
      cInv *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ ((1 : ℝ) / 4) * ‖N ξ‖ := by
      rw [integral_const_mul]
    _ =
      cInv *
        h3RawFinLerayOuterProductDivergenceQuarterMass
          (W t) (W t) i := by
      rfl
    _ ≤
      cInv *
        h3SelectedForcingQuarterMomentEnvelope ν A t :=
      mul_le_mul_of_nonneg_left
        hQuarterBound
        hcInv0
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        h3SelectedForcingQuarterMomentEnvelope ν A t := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
