import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Moment.FiveQuarterForcingEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdVariationFubini

/-!
# Full-third terminal variation from positive-time state envelopes

`FiveQuarterForcingEnvelope` packages the complete nonlinear forcing algebra
behind two scalar state envelopes:

    m₀(W(r)_k)    ≤ M₀,
    m₉/₄(W(r)_k) ≤ M₉.

For every coordinate, these imply

    m₅/₄(N(W(r),W(r))_i)
      ≤
    B₅(M₀,M₉).

The selected forcing-difference mass therefore obeys

    m₅/₄(N(W(s),W(s))_i - N(W(t),W(t))_i)
      ≤
    2 B₅(M₀,M₉)

throughout a positive terminal interval.

`ThirdVariationFubini` needs exactly such a uniform forcing-difference bound.
Consequently, uniform coordinatewise `m₀` and `m₉/₄` state envelopes on
`[a,t]` close product-space integrability of the full-third terminal variation
kernel.

The selected positive-time `9/4` theorem supplies all weighted integrability
needed below; only the numerical envelope inequalities are hypotheses.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdVariationStateEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted mass of a difference is at most the sum of the two weighted
masses. -/
theorem h3FourierFiveQuarterDifferenceMass_le_sum
    (F G : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F (volume : Measure H3FourierPoint3))
    (hG :
      Integrable G (volume : Measure H3FourierPoint3))
    (hF5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖)
      ≤
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖F ξ‖) +
      ∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖G ξ‖ := by
  have hDiff :=
    h3FourierFiveQuarterWeight_mul_norm_sub_integrable
      F G hF hG hF5 hG5

  have hSum := hF5.add hG5

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖
          ≤
        h3FourierFiveQuarterWeight ξ * ‖F ξ‖ +
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierFiveQuarterWeight ξ := by
      unfold h3FourierFiveQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖
          ≤
        h3FourierFiveQuarterWeight ξ * (‖F ξ‖ + ‖G ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (F ξ) (G ξ))
          hw
      _ =
        h3FourierFiveQuarterWeight ξ * ‖F ξ‖ +
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖ := by
        ring

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierFiveQuarterWeight ξ * ‖F ξ‖ +
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖) :=
      integral_mono hDiff hSum hPoint
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖ := by
      rw [integral_add hF5 hG5]

/-- Uniform positive-time `m₀` and `m₉/₄` state envelopes imply a uniform
`5/4` forcing-difference mass bound. -/
theorem h3SelectedForcingDifferenceFiveQuarterMass_le_stateEnvelope
    {ν A a t M0 M9 : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hM0 : 0 ≤ M0)
    (hM9 : 0 ≤ M9)
    (hState0 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M0)
    (hState9 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M9)
    (i : Fin 3)
    {s : ℝ}
    (hs : s ∈ Set.Ioo a t) :
    h3SelectedForcingDifferenceFiveQuarterMass
        ν A t hν U₀ hA hU₀ i s
      ≤
    2 * h3FiveQuarterForcingDiagonalEnvelope M0 M9 := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Ns : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  let Nt : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have ht0 : 0 < t :=
    lt_trans ha hat

  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hsIcc : s ∈ Set.Icc a t :=
    ⟨hs.1.le, hs.2.le⟩

  have htIcc : t ∈ Set.Icc a t :=
    ⟨hat.le, le_rfl⟩

  have hNs :
      Integrable Ns (volume : Measure H3FourierPoint3) := by
    dsimp only [Ns]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNt :
      Integrable Nt (volume : Measure H3FourierPoint3) := by
    dsimp only [Nt]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hNs5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖Ns ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Ns, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hNt5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖Nt ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Nt, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ ht0 htR i

  have hTriangle :=
    h3FourierFiveQuarterDifferenceMass_le_sum
      Ns Nt hNs hNt hNs5 hNt5

  have hWsq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (W s k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR k

  have hWtq :
      ∀ k : Fin 3,
        Integrable
          (fun ξ : H3FourierPoint3 =>
            h3FourierNineQuarterWeight ξ *
              ‖h3SpectralScalarRawFourier (W t k) ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro k
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
        hν U₀ hA hU₀ ht0 htR k

  have hWs0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (W s k) ≤ M0 := by
    intro k
    dsimp only [W]
    exact hState0 s hsIcc k

  have hWs9 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (W s k) ≤ M9 := by
    intro k
    dsimp only [W]
    exact hState9 s hsIcc k

  have hWt0 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass (W t k) ≤ M0 := by
    intro k
    dsimp only [W]
    exact hState0 t htIcc k

  have hWt9 :
      ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass (W t k) ≤ M9 := by
    intro k
    dsimp only [W]
    exact hState9 t htIcc k

  have hForceS :
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W s) (W s) i
        ≤
      h3FiveQuarterForcingDiagonalEnvelope M0 M9 :=
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_diagonalEnvelope
      (W s) i hM0 hM9 hWs0 hWs9 hWsq

  have hForceT :
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i
        ≤
      h3FiveQuarterForcingDiagonalEnvelope M0 M9 :=
    h3RawFinLerayOuterProductDivergenceFiveQuarterMass_le_diagonalEnvelope
      (W t) i hM0 hM9 hWt0 hWt9 hWtq

  have hSumForce :
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W s) (W s) i +
        h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i
        ≤
      2 * h3FiveQuarterForcingDiagonalEnvelope M0 M9 := by
    calc
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W s) (W s) i +
        h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i
          ≤
        h3FiveQuarterForcingDiagonalEnvelope M0 M9 +
          h3FiveQuarterForcingDiagonalEnvelope M0 M9 :=
        add_le_add hForceS hForceT
      _ =
        2 * h3FiveQuarterForcingDiagonalEnvelope M0 M9 := by
        ring

  have hTriangle' :
      (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖Ns ξ - Nt ξ‖)
        ≤
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W s) (W s) i +
        h3RawFinLerayOuterProductDivergenceFiveQuarterMass
          (W t) (W t) i := by
    simpa only [
      h3RawFinLerayOuterProductDivergenceFiveQuarterMass,
      Ns, Nt
    ] using hTriangle

  have hFinal :
      (∫ ξ : H3FourierPoint3,
          h3FourierFiveQuarterWeight ξ * ‖Ns ξ - Nt ξ‖)
        ≤
      2 * h3FiveQuarterForcingDiagonalEnvelope M0 M9 :=
    le_trans hTriangle' hSumForce

  simpa only [
    h3SelectedForcingDifferenceFiveQuarterMass,
    Ns, Nt, W
  ] using hFinal

/-- Uniform positive-time state envelopes close the full-third variation
Fubini step. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_stateEnvelope
    {ν A a t M0 M9 : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hM0 : 0 ≤ M0)
    (hM9 : 0 ≤ M9)
    (hState0 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierL1Mass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M0)
    (hState9 :
      ∀ r ∈ Set.Icc a t, ∀ k : Fin 3,
        h3SpectralScalarRawFourierNineQuarterMass
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ r k)
          ≤ M9)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailThirdVariationComplexKernel
        ν A t hν U₀ hA hU₀ i)
      (((volume : Measure ℝ).restrict (Set.Ioo a t)).prod
        (volume : Measure H3FourierPoint3)) := by
  let B : ℝ :=
    2 * h3FiveQuarterForcingDiagonalEnvelope M0 M9

  have hEnvelope0 :
      0 ≤ h3FiveQuarterForcingDiagonalEnvelope M0 M9 :=
    h3FiveQuarterForcingDiagonalEnvelope_nonneg hM0 hM9

  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (by norm_num) hEnvelope0

  apply
    h3SelectedDuhamelTailThirdVariationComplexKernel_fubini_integrable_of_fiveQuarterMass_le
      hν U₀ hA hU₀ ha hat htR hB i

  intro s hs

  dsimp only [B]

  exact
    h3SelectedForcingDifferenceFiveQuarterMass_le_stateEnvelope
      hν U₀ hA hU₀
      ha hat htR
      hM0 hM9
      hState0 hState9
      i hs

end
end Euclidean
end Bridge
end PrimeTensor
