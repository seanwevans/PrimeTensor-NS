import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Uniform.NineQuarter.Moment.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.State.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.Third.Variation.Mass

/-!
# Concrete quantitative selected full-third variation mass

The abstract full-third variation estimate now has all of its state inputs.

On every positive interval `[a,t]`:

* the selected restart path has the uniform raw Fourier `L¹` envelope
  `h3SelectedRestartRawFourierL1Envelope A`;
* `UniformNineQuarterMomentEnvelope` supplies the uniform raw Fourier `9/4`
  envelope
  `h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t`.

`ThirdVariationStateEnvelope` therefore gives the concrete forcing-difference
bound

    mass₅/₄(N_s - N_t)
      ≤
    2 * h3FiveQuarterForcingDiagonalEnvelope M₀ M₉.

`ThirdVariationMass` then integrates the normalized `-7/8` heat majorant and
produces the complete quantitative varying-source budget.

This file removes the final abstract numerical hypothesis from the selected
full-third variation term.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedThirdVariationMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform selected `5/4` forcing-difference envelope on `[a,t]`, obtained
from the selected `m₀` and interval-uniform `m₉/₄` state envelopes. -/
noncomputable def h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  2 *
    h3FiveQuarterForcingDiagonalEnvelope
      (h3SelectedRestartRawFourierL1Envelope A)
      (h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t)

/-- Concrete full-third variation budget for the selected restart path. -/
noncomputable def h3SelectedDuhamelTailThirdVariationUniformBudget
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelTailThirdVariationBudget
    ν a t
    (h3SelectedForcingDifferenceFiveQuarterUniformEnvelope ν A a t)

/-- The selected interval-uniform `9/4` state envelope is nonnegative on every
nonempty positive interval. -/
theorem h3SelectedMildNineQuarterMomentUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤ h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t := by
  let k0 : Fin 3 := 0

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have haR :
      a ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hat.le htR

  have hMass0 :
      0 ≤
        h3SpectralScalarRawFourierNineQuarterMass
          (W a k0) :=
    h3SpectralScalarRawFourierNineQuarterMass_nonneg
      (W a k0)

  have hBound0 :
      h3SpectralScalarRawFourierNineQuarterMass
          (W a k0)
        ≤
      h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t := by
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le_uniform_on
        hν U₀ hA hU₀ ha (le_refl a) hat.le htR k0
    dsimp only [W]
    simpa only [h3SpectralScalarRawFourierNineQuarterMass] using h

  exact le_trans hMass0 hBound0

/-- The selected forcing-difference envelope is nonnegative on a positive
terminal interval. -/
theorem h3SelectedForcingDifferenceFiveQuarterUniformEnvelope_nonneg
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A) :
    0 ≤ h3SelectedForcingDifferenceFiveQuarterUniformEnvelope ν A a t := by
  have hM0 :
      0 ≤ h3SelectedRestartRawFourierL1Envelope A :=
    h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM9 :
      0 ≤ h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t :=
    h3SelectedMildNineQuarterMomentUniformEnvelope_nonneg
      hν U₀ hA hU₀ ha hat htR

  unfold h3SelectedForcingDifferenceFiveQuarterUniformEnvelope

  exact
    mul_nonneg
      (by norm_num)
      (h3FiveQuarterForcingDiagonalEnvelope_nonneg hM0 hM9)

/-- The selected forcing difference has one explicit `5/4` raw Fourier mass
bound throughout the positive terminal interval `(a,t)`. -/
theorem h3SelectedForcingDifferenceFiveQuarterMass_le_uniformEnvelope
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    {s : ℝ}
    (hs : s ∈ Set.Ioo a t) :
    h3SelectedForcingDifferenceFiveQuarterMass
        ν A t hν U₀ hA hU₀ i s
      ≤
    h3SelectedForcingDifferenceFiveQuarterUniformEnvelope ν A a t := by
  let M0 : ℝ :=
    h3SelectedRestartRawFourierL1Envelope A

  let M9 : ℝ :=
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t

  have hM0 :
      0 ≤ M0 := by
    dsimp only [M0]
    exact
      h3SelectedRestartRawFourierL1Envelope_nonneg hA.le

  have hM9 :
      0 ≤ M9 := by
    dsimp only [M9]
    exact
      h3SelectedMildNineQuarterMomentUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hState0 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M0 := by
    dsimp only [M0]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourierL1Mass_intervalEnvelope
        (a := a) (t := t)
        hν U₀ hA hU₀

  have hState9 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M9 := by
    intro r hr k
    dsimp only [M9]
    have h :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le_uniform_on
        hν U₀ hA hU₀ ha hr.1 hr.2 htR k
    simpa only [h3SpectralScalarRawFourierNineQuarterMass] using h

  have hBase :=
    h3SelectedForcingDifferenceFiveQuarterMass_le_stateEnvelope
      (M0 := M0)
      (M9 := M9)
      hν U₀ hA hU₀
      ha hat htR
      hM0 hM9
      hState0 hState9
      i hs

  unfold h3SelectedForcingDifferenceFiveQuarterUniformEnvelope
  dsimp only [M0, M9] at hBase ⊢
  exact hBase

/-- Fully concrete quantitative full-third selected variation estimate. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_iteratedNormIntegral_le_uniformEnvelope
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
          ‖h3SelectedDuhamelTailThirdVariationComplexKernel
            ν A t hν U₀ hA hU₀ i (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt)
      ≤
    h3SelectedDuhamelTailThirdVariationUniformBudget ν A a t := by
  dsimp only

  let B : ℝ :=
    h3SelectedForcingDifferenceFiveQuarterUniformEnvelope ν A a t

  have hB : 0 ≤ B := by
    dsimp only [B]
    exact
      h3SelectedForcingDifferenceFiveQuarterUniformEnvelope_nonneg
        hν U₀ hA hU₀ ha hat htR

  have hMassI :
      ∀ s ∈ Set.Ioo a t,
        h3SelectedForcingDifferenceFiveQuarterMass
          ν A t hν U₀ hA hU₀ i s ≤ B := by
    intro s hs
    dsimp only [B]
    exact
      h3SelectedForcingDifferenceFiveQuarterMass_le_uniformEnvelope
        hν U₀ hA hU₀ ha hat htR i hs

  have hBase :=
    h3SelectedDuhamelTailThirdVariationComplexKernel_iteratedNormIntegral_le_of_fiveQuarterMass_le
      (B := B)
      hν U₀ hA hU₀
      ha hat htR
      hB i hMassI

  unfold h3SelectedDuhamelTailThirdVariationUniformBudget
  exact hBase

end
end Euclidean
end Bridge
end PrimeTensor
