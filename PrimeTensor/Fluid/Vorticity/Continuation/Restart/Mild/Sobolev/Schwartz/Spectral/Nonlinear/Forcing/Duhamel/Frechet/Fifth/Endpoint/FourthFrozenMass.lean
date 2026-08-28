import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.SecondForcingMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdFrozenMass

/-!
# Fifth Fréchet endpoint: quantitative frozen fourth-moment terminal tail

The selected forcing now has a quantitative second raw Fourier moment.

For the frozen terminal contribution at full fourth weight,

    |ξ|⁴ = |ξ|² · |ξ|².

The second factor is absorbed by the exact terminal-half heat primitive already
used by `ThirdFrozenMass`:

    ∫_{t/2}^t |ξ|² |H_{t-s}(ξ) N_t(ξ)| ds
      ≤
    (((2π)^2 ν)⁻¹) |N_t(ξ)|.

Therefore

    ∫_{t/2}^t |ξ|⁴ |H_{t-s}(ξ) N_t(ξ)| ds
      ≤
    (((2π)^2 ν)⁻¹) |ξ|² |N_t(ξ)|,

and the remaining frequency integral is exactly the selected forcing second
mass closed in `SecondForcingMass`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFourthFrozenMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Selected frozen terminal contribution after inserting the radial fourth
Fourier weight. -/
noncomputable def h3SelectedDuhamelTailFourthFrozenComplexKernel
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
  ((‖p.2‖ ^ 4 : ℝ) : ℂ) *
    (h3HeatFourierSymbol ν (t - p.1) p.2 *
      h3RawFinLerayOuterProductDivergence
        (W t) (W t) i p.2)

/-- Explicit frozen fourth-moment budget. -/
noncomputable def h3SelectedDuhamelTailFourthFrozenBudget
    (ν A t : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    h3SelectedForcingSecondMomentEnvelope ν A t

/-- Joint strong measurability of the selected frozen radial-fourth kernel. -/
theorem h3SelectedDuhamelTailFourthFrozenComplexKernel_aestronglyMeasurable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3SelectedDuhamelTailFourthFrozenComplexKernel
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
          ‖p.2‖ ^ 4) :=
    (continuous_norm.comp continuous_snd).pow 4

  have hWeight :
      AEStronglyMeasurable
        (fun p : ℝ × H3FourierPoint3 =>
          ((‖p.2‖ ^ 4 : ℝ) : ℂ))
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

  unfold h3SelectedDuhamelTailFourthFrozenComplexKernel
  dsimp only [W]
  exact hWeight.mul hFrozen

/-- The selected frozen radial-fourth terminal kernel is genuinely integrable
on source-time × frequency. -/
theorem h3SelectedDuhamelTailFourthFrozenComplexKernel_fubini_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailFourthFrozenComplexKernel
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
        (h3SelectedDuhamelTailFourthFrozenComplexKernel
          ν A t hν U₀ hA hU₀ i)
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [μt]
    exact
      h3SelectedDuhamelTailFourthFrozenComplexKernel_aestronglyMeasurable
        hν U₀ hA hU₀ i

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv * (‖ξ‖ ^ 2 * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hSecond.const_mul cInv

  refine (integrable_prod_iff' hJoint).2 ?_
  constructor

  · exact Filter.Eventually.of_forall fun ξ => by
      have hSecCont :
          Continuous
            (fun s : ℝ =>
              h3SelectedDuhamelTailFourthFrozenComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)) := by
        unfold h3SelectedDuhamelTailFourthFrozenComplexKernel
        dsimp only
        unfold h3HeatFourierSymbol
        fun_prop

      have hSecInterval :
          IntervalIntegrable
            (fun s : ℝ =>
              h3SelectedDuhamelTailFourthFrozenComplexKernel
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
              ‖h3SelectedDuhamelTailFourthFrozenComplexKernel
                ν A t hν U₀ hA hU₀ i (s, ξ)‖
              ∂μt)
          (volume : Measure H3FourierPoint3) :=
      hJoint.prod_swap.norm.integral_prod_right'

    refine hMajor.mono' hOuterMeas ?_
    filter_upwards with ξ

    have hNorm0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hWeight0 :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg hNorm0 4

    have hSquare0 :
        0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg hNorm0 2

    have hInnerEq :
        (∫ s : ℝ,
            ‖h3SelectedDuhamelTailFourthFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt)
          =
        ‖ξ‖ ^ 2 *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      rw [← integral_const_mul]
      dsimp only [μt]
      apply integral_congr_ae
      filter_upwards with s
      unfold h3SelectedDuhamelTailFourthFrozenComplexKernel
      dsimp only [N, W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hWeight0]
      rw [norm_mul]
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
            ‖h3SelectedDuhamelTailFourthFrozenComplexKernel
              ν A t hν U₀ hA hU₀ i (s, ξ)‖
            ∂μt :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun s => norm_nonneg _)

    rw [Real.norm_eq_abs, abs_of_nonneg hInnerNonneg]
    rw [hInnerEq]

    calc
      ‖ξ‖ ^ 2 *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        ‖ξ‖ ^ 2 * (cInv * ‖N ξ‖) :=
      mul_le_mul_of_nonneg_left hSecondBound hSquare0
      _ =
        cInv * (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        ring

/-- Quantitative frozen fourth-moment budget, in source-time-outer
orientation. -/
theorem h3SelectedDuhamelTailFourthFrozenComplexKernel_iteratedNormIntegral_le
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
          ‖h3SelectedDuhamelTailFourthFrozenComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelTailFourthFrozenBudget ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let N : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailFourthFrozenComplexKernel
      ν A t hν U₀ hA hU₀ i

  let cInv : ℝ :=
    ((2 * Real.pi) ^ 2 * ν)⁻¹

  have hProd :
      Integrable
        Z
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailFourthFrozenComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hSwap :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
        ∂μt := by
    exact
      MeasureTheory.integral_integral_swap
        (f := fun s : ℝ => fun ξ : H3FourierPoint3 => ‖Z (s, ξ)‖)
        hProd.norm

  have hOuter :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
        (volume : Measure H3FourierPoint3) :=
    hProd.integral_norm_prod_right

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖N ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [N, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          cInv * (‖ξ‖ ^ 2 * ‖N ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hSecond.const_mul cInv

  have hhalf : t / 2 ≤ t := by
    linarith

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        (∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
          ≤
        cInv * (‖ξ‖ ^ 2 * ‖N ξ‖) := by
    intro ξ

    have hNorm0 : 0 ≤ ‖ξ‖ :=
      norm_nonneg ξ

    have hWeight0 :
        0 ≤ ‖ξ‖ ^ 4 :=
      pow_nonneg hNorm0 4

    have hSquare0 :
        0 ≤ ‖ξ‖ ^ 2 :=
      pow_nonneg hNorm0 2

    have hInnerEq :
        (∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
          =
        ‖ξ‖ ^ 2 *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖) := by
      rw [intervalIntegral.integral_of_le hhalf]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      rw [← integral_const_mul]
      dsimp only [Z, μt]
      apply integral_congr_ae
      filter_upwards with s
      unfold h3SelectedDuhamelTailFourthFrozenComplexKernel
      dsimp only [N, W]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hWeight0]
      rw [norm_mul]
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
      ‖ξ‖ ^ 2 *
          (∫ s in (t / 2)..t,
            ‖ξ‖ ^ 2 *
              ‖h3HeatFourierSymbol ν (t - s) ξ * N ξ‖)
          ≤
        ‖ξ‖ ^ 2 * (cInv * ‖N ξ‖) :=
      mul_le_mul_of_nonneg_left hSecondBound hSquare0
      _ =
        cInv * (‖ξ‖ ^ 2 * ‖N ξ‖) := by
        ring

  have hFreq :
      (∫ ξ : H3FourierPoint3,
          ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt)
        ≤
      ∫ ξ : H3FourierPoint3,
        cInv * (‖ξ‖ ^ 2 * ‖N ξ‖) :=
    integral_mono hOuter hMajor hPoint

  have hForce :
      h3RawFinLerayOuterProductDivergenceSecondMass
          (W t) (W t) i
        ≤
      h3SelectedForcingSecondMomentEnvelope ν A t := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le
        hν U₀ hA hU₀ ht htR i

  have hc0 : 0 ≤ cInv := by
    dsimp only [cInv]
    positivity

  unfold h3SelectedDuhamelTailFourthFrozenBudget

  calc
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖Z (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ, ‖Z (s, ξ)‖ ∂μt :=
      hSwap
    _ ≤
      ∫ ξ : H3FourierPoint3,
        cInv * (‖ξ‖ ^ 2 * ‖N ξ‖) :=
      hFreq
    _ =
      cInv *
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 * ‖N ξ‖ := by
      rw [integral_const_mul]
    _ =
      cInv *
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W t) (W t) i := by
      rfl
    _ ≤
      cInv *
        h3SelectedForcingSecondMomentEnvelope ν A t :=
      mul_le_mul_of_nonneg_left hForce hc0
    _ =
      (((2 * Real.pi) ^ 2 * ν)⁻¹) *
        h3SelectedForcingSecondMomentEnvelope ν A t := by
      rfl

end
end Euclidean
end Bridge
end PrimeTensor
