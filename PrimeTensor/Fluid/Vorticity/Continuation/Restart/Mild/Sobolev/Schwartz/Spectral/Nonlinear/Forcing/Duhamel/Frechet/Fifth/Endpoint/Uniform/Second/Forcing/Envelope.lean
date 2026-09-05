import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Uniform.Third.Moment.Envelope

/-!
# Fifth Fréchet endpoint: uniform selected second forcing envelope

The selected mild path now has one cubic raw Fourier mass constant valid on
every positive interval `[a,t]`.

The pointwise second forcing envelope depends on time only through that cubic
state envelope:

    B₂(r)
      =
    2 ∑ₖ ∑ⱼ (2π) C₃
      (M₃(r) M₀ + M₀ M₃(r)).

Replacing `M₃(r)` by the interval-uniform cubic state constant therefore gives
one forcing second-moment bound valid throughout `[a,t]`.

This file also substitutes that concrete bound into the abstract `15/4`
source-time theorem.  Thus the fifth layer obtains a completely explicit
subcritical Duhamel source budget

    B₂^[a,t] · 8 C₇(ν) (t-a)^(1/8).

No convolution, divergence, Leray, or Fubini estimate is reopened.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointUniformSecondForcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform selected forcing second-moment envelope on `[a,t]`. -/
noncomputable def h3SelectedForcingSecondMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    ∑ _k : Fin 3,
      ∑ _j : Fin 3,
        (2 * Real.pi) *
          (h3FourierThirdSplitCoefficient *
            (h3SelectedMildThirdMomentUniformEnvelope ν A a t *
                h3SelectedRestartRawFourierL1Envelope A +
              h3SelectedRestartRawFourierL1Envelope A *
                h3SelectedMildThirdMomentUniformEnvelope ν A a t))

/-- The pointwise selected forcing second-moment envelope is dominated by the
interval-uniform one whenever `r ∈ [a,t]`. -/
theorem h3SelectedForcingSecondMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    h3SelectedForcingSecondMomentEnvelope ν A r
      ≤
    h3SelectedForcingSecondMomentUniformEnvelope ν A a t := by
  have hM3 :=
    h3SelectedMildThirdMomentEnvelope_le_uniform_on
      hν U₀ hA hU₀ ha har hrt htR

  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hLeft :
      h3SelectedMildThirdMomentEnvelope ν A r *
          h3SelectedRestartRawFourierL1Envelope A
        ≤
      h3SelectedMildThirdMomentUniformEnvelope ν A a t *
          h3SelectedRestartRawFourierL1Envelope A :=
    mul_le_mul_of_nonneg_right hM3 hM0

  have hRight :
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildThirdMomentEnvelope ν A r
        ≤
      h3SelectedRestartRawFourierL1Envelope A *
          h3SelectedMildThirdMomentUniformEnvelope ν A a t :=
    mul_le_mul_of_nonneg_left hM3 hM0

  have hPair :
      h3SelectedMildThirdMomentEnvelope ν A r *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildThirdMomentEnvelope ν A r
        ≤
      h3SelectedMildThirdMomentUniformEnvelope ν A a t *
            h3SelectedRestartRawFourierL1Envelope A +
          h3SelectedRestartRawFourierL1Envelope A *
            h3SelectedMildThirdMomentUniformEnvelope ν A a t :=
    add_le_add hLeft hRight

  have hSplit0 :
      0 ≤ h3FourierThirdSplitCoefficient := by
    unfold h3FourierThirdSplitCoefficient
    norm_num

  have hWeighted :
      h3FourierThirdSplitCoefficient *
          (h3SelectedMildThirdMomentEnvelope ν A r *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildThirdMomentEnvelope ν A r)
        ≤
      h3FourierThirdSplitCoefficient *
          (h3SelectedMildThirdMomentUniformEnvelope ν A a t *
              h3SelectedRestartRawFourierL1Envelope A +
            h3SelectedRestartRawFourierL1Envelope A *
              h3SelectedMildThirdMomentUniformEnvelope ν A a t) :=
    mul_le_mul_of_nonneg_left hPair hSplit0

  have hTerm :
      ∀ k j : Fin 3,
        (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SelectedMildThirdMomentEnvelope ν A r *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildThirdMomentEnvelope ν A r))
          ≤
        (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SelectedMildThirdMomentUniformEnvelope ν A a t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildThirdMomentUniformEnvelope ν A a t)) := by
    intro _k _j
    exact
      mul_le_mul_of_nonneg_left hWeighted (by positivity)

  have hSum :
      (∑ k : Fin 3,
          ∑ j : Fin 3,
            (2 * Real.pi) *
              (h3FourierThirdSplitCoefficient *
                (h3SelectedMildThirdMomentEnvelope ν A r *
                    h3SelectedRestartRawFourierL1Envelope A +
                  h3SelectedRestartRawFourierL1Envelope A *
                    h3SelectedMildThirdMomentEnvelope ν A r)))
        ≤
      ∑ k : Fin 3,
        ∑ j : Fin 3,
          (2 * Real.pi) *
            (h3FourierThirdSplitCoefficient *
              (h3SelectedMildThirdMomentUniformEnvelope ν A a t *
                  h3SelectedRestartRawFourierL1Envelope A +
                h3SelectedRestartRawFourierL1Envelope A *
                  h3SelectedMildThirdMomentUniformEnvelope ν A a t)) :=
    Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun j _ =>
        hTerm k j

  unfold
    h3SelectedForcingSecondMomentEnvelope
    h3SelectedForcingSecondMomentUniformEnvelope

  exact
    mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- Every selected forcing coordinate has second raw Fourier mass bounded by
one explicit constant throughout `[a,t]`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_uniform_on
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
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3RawFinLerayOuterProductDivergenceSecondMass
        (W r) (W r) i
      ≤
    h3SelectedForcingSecondMomentUniformEnvelope ν A a t := by
  dsimp only

  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hPoint :=
    h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le
      hν U₀ hA hU₀ hr hrR i

  exact
    le_trans hPoint
      (h3SelectedForcingSecondMomentEnvelope_le_uniform_on
        hν U₀ hA hU₀ ha har hrt htR)

/-- The uniform selected forcing second-moment envelope is nonnegative on every
nonempty positive interval. -/
theorem h3SelectedForcingSecondMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤ h3SelectedForcingSecondMomentUniformEnvelope ν A a t := by
  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM3 :
      0 ≤ h3SelectedMildThirdMomentUniformEnvelope ν A a t :=
    h3SelectedMildThirdMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  have hSplit0 :
      0 ≤ h3FourierThirdSplitCoefficient := by
    unfold h3FourierThirdSplitCoefficient
    norm_num

  unfold h3SelectedForcingSecondMomentUniformEnvelope

  exact
    mul_nonneg
      (by norm_num)
      (Finset.sum_nonneg fun _k _ => by
        exact
          Finset.sum_nonneg fun _j _ => by
            exact
              mul_nonneg
                (by positivity)
                (mul_nonneg
                  hSplit0
                  (add_nonneg
                    (mul_nonneg hM3 hM0)
                    (mul_nonneg hM0 hM3))))

/-- Fully concrete selected `15/4` Duhamel source budget on `(a,t)`. -/
noncomputable def h3SelectedDuhamelFifteenQuarterUniformBudget
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelFifteenQuarterSourceBudget
    ν a t
    (h3SelectedForcingSecondMomentUniformEnvelope ν A a t)

/-- The selected `15/4` Duhamel source kernel is genuinely integrable on every
positive source interval, with all forcing-envelope hypotheses discharged. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_uniformEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelFifteenQuarterComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let B : ℝ :=
    h3SelectedForcingSecondMomentUniformEnvelope ν A a t

  have hB : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingSecondMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  exact
    h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_of_secondMass_le
      (B := B)
      hν U₀ hA hU₀
      ha hat htR
      hB i hMassI

/-- Fully concrete quantitative selected `15/4` source-time norm budget. -/
theorem h3SelectedDuhamelFifteenQuarterComplexKernel_iteratedNormIntegral_le_uniformEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let μt : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Ioo a t)
    (∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖h3SelectedDuhamelFifteenQuarterComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelFifteenQuarterUniformBudget ν A a t := by
  dsimp only

  let B : ℝ :=
    h3SelectedForcingSecondMomentUniformEnvelope ν A a t

  have hB : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingSecondMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        let W : ℝ → H3SpectralFinVectorState :=
          h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀
        h3RawFinLerayOuterProductDivergenceSecondMass
          (W s) (W s) i ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMass_le_uniform_on
        hν U₀ hA hU₀
        ha hs.1.le hs.2.le htR i

  have hBase :=
    h3SelectedDuhamelFifteenQuarterComplexKernel_iteratedNormIntegral_le_of_secondMass_le
      (B := B)
      hν U₀ hA hU₀
      ha hat htR
      hB i hMassI

  unfold h3SelectedDuhamelFifteenQuarterUniformBudget
  exact hBase

end
end Euclidean
end Bridge
end PrimeTensor
