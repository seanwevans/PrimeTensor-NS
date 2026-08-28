import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FourthMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterNamedTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.UniformSecondForcingEnvelope

/-!
# Fifth Fréchet endpoint: interval-uniform fifteen-quarter terminal-tail mass

The selected full-fourth source mass now only needs one interval-uniform
`11/4` forcing constant.  That forcing constant is built from a uniform
`15/4` state bound.

The only nested part of the pointwise `15/4` state envelope is the terminal
tail on `(r/2,r)`.  Instead of proving monotonicity of the already-packaged
local tail budget, this file reuses the abstract `15/4` Fubini theorem with
one larger forcing-second constant valid on the containing interval

    (r/2,r) ⊂ (a/2,t).

Thus every selected `15/4` terminal tail for `r ∈ [a,t]` is bounded by the
single explicit budget

    SourceBudget(ν, a/2, t, B₂^[a/2,t]).

No nonlinear or heat estimate is reopened.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointUniformFifteenQuarterTailMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One enlarged `15/4` terminal-tail budget valid for every `r ∈ [a,t]`. -/
noncomputable def h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelFifteenQuarterSourceBudget
    ν (a / 2) t
    (h3SelectedForcingSecondMomentUniformEnvelope
      ν A (a / 2) t)

/-- The global forcing-second constant on `[a/2,t]` is nonnegative. -/
theorem h3SelectedForcingSecondMomentUniformEnvelope_halfGlobal_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤
      h3SelectedForcingSecondMomentUniformEnvelope
        ν A (a / 2) t := by
  have ha2 : 0 < a / 2 := by
    positivity

  have ha2t : a / 2 < t := by
    linarith

  exact
    h3SelectedForcingSecondMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha2 ha2t htR

/-- Every actual selected forcing-second mass occurring in a local terminal
half `(r/2,r)` is bounded by the one global constant on `[a/2,t]`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_halfGlobal
    {ν A a r t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo (r / 2) r)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceSecondMass
        (W s) (W s) i
      ≤
    h3SelectedForcingSecondMomentUniformEnvelope
      ν A (a / 2) t := by
  dsimp only

  have ha2 : 0 < a / 2 := by
    positivity

  have ha2s : a / 2 ≤ s := by
    have har2 : a / 2 ≤ r / 2 := by
      linarith
    exact le_trans har2 hs.1.le

  have hst : s ≤ t := by
    exact le_trans hs.2.le hrt

  exact
    h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_uniform_on
      hν U₀ hA hU₀
      ha2 ha2s hst htR i

/-- The local `15/4` source budget with the global forcing constant is bounded
by the enlarged interval budget on `(a/2,t)`. -/
theorem h3SelectedDuhamelFifteenQuarterSourceBudget_local_le_halfGlobal
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedDuhamelFifteenQuarterSourceBudget
        ν (r / 2) r
        (h3SelectedForcingSecondMomentUniformEnvelope
          ν A (a / 2) t)
      ≤
    h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
      ν A a t := by
  let B : ℝ :=
    h3SelectedForcingSecondMomentUniformEnvelope
      ν A (a / 2) t

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingSecondMomentUniformEnvelope_halfGlobal_nonneg
        hν U₀ hA hU₀ ha
        (le_trans har hrt) htR

  have hLocalLag0 :
      0 ≤ r - r / 2 := by
    have hr0 : 0 ≤ r :=
      le_trans ha.le har
    linarith

  have hGlobalLag0 :
      0 ≤ t - a / 2 := by
    linarith

  have hLag :
      r - r / 2 ≤ t - a / 2 := by
    linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      (t - a / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow
      hLocalLag0 hLag (by norm_num)

  have hScale0 :
      0 ≤
        8 * h3HeatSevenQuarterNormalizedCoefficient ν := by
    unfold h3HeatSevenQuarterNormalizedCoefficient
    positivity

  have hScaled :
      8 * h3HeatSevenQuarterNormalizedCoefficient ν *
          (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      8 * h3HeatSevenQuarterNormalizedCoefficient ν *
          (t - a / 2) ^ ((1 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left hPow hScale0

  unfold
    h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
    h3SelectedDuhamelFifteenQuarterSourceBudget

  exact
    mul_le_mul_of_nonneg_left
      hScaled hB0

/-- The weighted `15/4` terminal-tail amplitude at any `r ∈ [a,t]` is bounded
by the enlarged global tail budget. -/
theorem integral_norm_h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_le_intervalUniform
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A r hν U₀ hA hU₀ i ξ‖)
      ≤
    h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
      ν A a t := by
  let B : ℝ :=
    h3SelectedForcingSecondMomentUniformEnvelope
      ν A (a / 2) t

  let μr : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (r / 2) r)

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelFifteenQuarterComplexKernel
      ν A r hν U₀ hA hU₀ i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ∫ s : ℝ,
        ‖Z (s, ξ)‖
        ∂μr

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hhalf0 : 0 < r / 2 := by
    positivity

  have hhalf : r / 2 < r := by
    linarith

  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingSecondMomentUniformEnvelope_halfGlobal_nonneg
        hν U₀ hA hU₀ ha
        (le_trans har hrt) htR

  have hMassI :
      ∀ s ∈ Set.Ioo (r / 2) r,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_halfGlobal
        hν U₀ hA hU₀ ha har hrt htR hs i

  have hProd :
      Integrable
        Z
        (μr.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μr]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_of_secondMass_le
        (B := B)
        hν U₀ hA hU₀
        hhalf0 hhalf hrR
        hB0 i hMassI

  have hWeightedInt :
      Integrable
        (h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A r hν U₀ hA hU₀ i)
        (volume : Measure H3FourierPoint3) := by
    have hOuter := hProd.integral_prod_right
    unfold h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
    exact hOuter

  have hWeightedNormInt :=
    hWeightedInt.norm

  have hMInt :
      Integrable M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M]
    exact hProd.integral_norm_prod_right

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
            ν A r hν U₀ hA hU₀ i ξ‖
          ≤
        M ξ := by
    intro ξ
    calc
      ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A r hν U₀ hA hU₀ i ξ‖
          =
        ‖∫ s : ℝ,
            Z (s, ξ)
            ∂μr‖ := by
          rfl
      _ ≤
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
          ∂μr :=
        norm_integral_le_integral_norm _
      _ =
        M ξ := by
          rfl

  have hOuterLe :
      (∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
            ν A r hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
    integral_mono
      hWeightedNormInt
      hMInt
      hPointwise

  have hSwap :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μr)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
        ∂μr := by
    exact
      MeasureTheory.integral_integral_swap
        (f := fun s : ℝ => fun ξ : H3FourierPoint3 => ‖Z (s, ξ)‖)
        hProd.norm

  have hLocalBudget :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μr)
        ≤
      h3SelectedDuhamelFifteenQuarterSourceBudget
        ν (r / 2) r B := by
    dsimp only [Z, μr]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_iteratedNormIntegral_le_of_secondMass_le
        (B := B)
        hν U₀ hA hU₀
        hhalf0 hhalf hrR
        hB0 i hMassI

  have hGlobalBudget :
      h3SelectedDuhamelFifteenQuarterSourceBudget
          ν (r / 2) r B
        ≤
      h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
        ν A a t := by
    dsimp only [B]
    exact
      h3SelectedDuhamelFifteenQuarterSourceBudget_local_le_halfGlobal
        hν U₀ hA hU₀ ha har hrt htR

  calc
    (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A r hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
      hOuterLe
    _ =
      ∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖Z (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μr :=
      hSwap.symm
    _ ≤
      h3SelectedDuhamelFifteenQuarterSourceBudget
        ν (r / 2) r B :=
      hLocalBudget
    _ ≤
      h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
        ν A a t :=
      hGlobalBudget

/-- Every actual raw selected terminal-tail amplitude has `15/4` mass bounded
by the one enlarged interval budget. -/
theorem integral_fifteenQuarterMoment_h3SelectedDuhamelTailRawFourierAmplitude_le_intervalUniform
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A r hν U₀ hA hU₀ i ξ‖)
      ≤
    h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
      ν A a t := by
  have hWeighted :=
    integral_norm_h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_le_intervalUniform
      hν U₀ hA hU₀ ha har hrt htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SelectedDuhamelTailRawFourierAmplitude
              ν A r hν U₀ hA hU₀ i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A r hν U₀ hA hU₀ i ξ‖ := by
    apply integral_congr_ae
    filter_upwards with ξ

    have hWeight0 :
        0 ≤ h3FourierFifteenQuarterWeight ξ := by
      unfold h3FourierFifteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    rw [
      h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_eq_weight_mul_raw
        hν U₀ hA hU₀ i ξ,
      norm_mul,
      Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg hWeight0
    ]

  rw [hIntegralEq]
  exact hWeighted

/-- Every named selected terminal-tail `L²` state has `15/4` mass bounded by
the same enlarged interval budget. -/
theorem integral_fifteenQuarterMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le_intervalUniform
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelFifteenQuarterTailIntervalUniformBudget
      ν A a t := by
  have hr :
      0 < r :=
    lt_of_lt_of_le ha har

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_fifteenQuarterMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ hr i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := r) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A r hν U₀ hA hU₀ i ξ‖ :=
    integral_congr_ae hEq

  have hRaw :=
    integral_fifteenQuarterMoment_h3SelectedDuhamelTailRawFourierAmplitude_le_intervalUniform
      hν U₀ hA hU₀ ha har hrt htR i

  exact hIntegralEq.trans_le hRaw

end
end Euclidean
end Bridge
end PrimeTensor
