import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterFrozenMass

/-!
# Quantitative mass budget for the selected nine-quarter variation tail

The varying terminal-half contribution is already controlled pointwise in
source time by the normalized cancellation majorant

    M(s)
      =
    C(ν,K) (t-s)^(-7/8),

where

    K =
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (t/2) t.

`NineQuarterMajorant` proves the exact primitive

    ∫_{t/2}^t M(s) ds
      =
    8 C(ν,K) (t-t/2)^(1/8).

`NineQuarterVariationFubini` already proves genuine product integrability and
the frequency-section domination by `M`.

This file merely integrates that existing domination.  The resulting
variation budget is therefore

    8 C(ν,K) (t-t/2)^(1/8).

Together with `NineQuarterFrozenMass`, this gives both quantitative pieces of
the selected terminal-half `9/4` tail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterVariationMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit source-time budget for the varying selected `9/4` terminal-half
contribution. -/
noncomputable def h3SelectedDuhamelTailNineQuarterVariationBudget
    (ν A t : ℝ) : ℝ :=
  let K : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (t / 2) t
  8 *
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
      ν K *
    (t - t / 2) ^ ((1 : ℝ) / 8)

/-- The iterated source-time/frequency norm integral of the selected `9/4`
variation kernel is bounded by the exact normalized `-7/8` majorant
primitive. -/
theorem h3SelectedDuhamelTailNineQuarterVariationComplexKernel_iteratedNormIntegral_le
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
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelTailNineQuarterVariationBudget ν A t := by
  dsimp only

  let K : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (t / 2) t

  let M : ℝ → ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant
      ν t K

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

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
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel_aestronglyMeasurable
        (t := t) hν U₀ hA hU₀ i

  have hProd :
      Integrable
        (h3SelectedDuhamelTailNineQuarterVariationComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailNineQuarterVariationComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hOuter :
      Integrable
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
        μt := by
    exact
      ((integrable_prod_iff hJoint).1 hProd).2

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
      Integrable M μt := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalfLe] at hMajorInterval
    rw [integrableOn_Ioc_iff_integrableOn_Ioo] at hMajorInterval
    dsimp only [μt]
    exact hMajorInterval

  have hDom :
      ∀ᵐ s : ℝ ∂μt,
        (∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖)
          ≤
        M s := by
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

    rw [hOuterEq]

    dsimp only [M, K, W]

    exact
      h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_nineQuarter_le_majorant_selectedRestart
        hν U₀ hA hU₀ hhalfPos hhalfLt htR hs i

  have hIntegral :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      ∫ s : ℝ, M s ∂μt :=
    integral_mono_ae hOuter hMajor hDom

  have hMajorIntegralEq :
      (∫ s : ℝ, M s ∂μt)
        =
      ∫ s in (t / 2)..t, M s := by
    rw [intervalIntegral.integral_of_le hhalfLe]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hExact :
      (∫ s in (t / 2)..t, M s)
        =
      8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν K *
        (t - t / 2) ^ ((1 : ℝ) / 8) := by
    dsimp only [M]
    exact
      h3NonlinearForcingHeatNineQuarterQuarterCancellationMajorant_integral_on
        hhalfLe

  unfold h3SelectedDuhamelTailNineQuarterVariationBudget

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailNineQuarterVariationComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
        ≤
      ∫ s : ℝ, M s ∂μt :=
      hIntegral
    _ =
      ∫ s in (t / 2)..t, M s :=
      hMajorIntegralEq
    _ =
      8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν K *
        (t - t / 2) ^ ((1 : ℝ) / 8) :=
      hExact
    _ =
      8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (t / 2) t) *
        (t - t / 2) ^ ((1 : ℝ) / 8) := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
