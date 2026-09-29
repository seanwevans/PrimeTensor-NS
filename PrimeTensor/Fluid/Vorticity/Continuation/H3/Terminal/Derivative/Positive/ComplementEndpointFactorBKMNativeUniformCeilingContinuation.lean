import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeRateSelection
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSubtail
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.FullEnergyDissipationCascade

/-!
# A uniform indexed ceiling forces continuation

Quantitative native witnesses are closed under cofinal reindexing. If raw
dissipation diverges on one such witness, its indices can be selected so that
it exceeds any prescribed finite bound at the new index. Consequently, a raw
dissipation ceiling imposed on *every* quantitative native witness cannot hold
under hypothetical nonextension. The rate in the ceiling is immaterial to
this argument; its square-root exponential form is retained here to match
the existing interface.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Divergent raw dissipation on a quantitative native witness is
incompatible with the indexed ceiling on every such witness. -/
theorem not_nativeUniformRawSubexponentialCeiling_of_rawDissipationTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawTop : Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop) :
    ¬ H3TerminalNativeUniformRawSubexponentialCeiling u b T := by
  classical
  intro hCeiling
  let rate : ℕ → ℝ := fun n =>
    Real.exp ((1 : ℝ) * Real.sqrt ((n : ℝ) + 1)) ^ 2
  have hPick : ∀ n : ℕ, ∃ j : ℕ,
      n ≤ j ∧ rate n < velocityH3DissipationAt u (τ j) := by
    intro n
    have hLarge : ∀ᶠ j : ℕ in atTop,
        rate n < velocityH3DissipationAt u (τ j) :=
      hRawTop.eventually (eventually_gt_atTop (rate n))
    obtain ⟨j, hjIndex, hjLarge⟩ :=
      ((eventually_ge_atTop n).and hLarge).exists
    exact ⟨j, hjIndex, hjLarge⟩
  choose k hk using hPick
  have hCofinal : ∀ n : ℕ, n ≤ k n := fun n => (hk n).1
  have hReindexed : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient
        (fun n => τ (k n)) (fun n => y (k n)) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hCofinal
  have hUpper := hCeiling p sCurl sGradient
    (fun n => τ (k n)) (fun n => y (k n)) hReindexed 1 (by norm_num)
  change ∀ᶠ n : ℕ in atTop,
    velocityH3DissipationAt u (τ (k n)) ≤ rate n at hUpper
  obtain ⟨n, hnUpper⟩ := hUpper.exists
  exact (not_lt_of_ge hnUpper) (hk n).2

/-- On any strict terminal subtail, hypothetical nonextension excludes
the ceiling quantified over all quantitative native witnesses. -/
theorem not_nativeUniformRawSubexponentialCeiling_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    ¬ H3TerminalNativeUniformRawSubexponentialCeiling u b T := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
      hH3 hNoExtension hClass hb
  have hAt := hData.1
  have hTau := hData.2.1
  have hTauLT : Tendsto τ atTop (𝓝[<] T) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hTau, Eventually.of_forall (fun n => (hAt n).1.2)⟩
  have hRawTop : Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop :=
    (velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT
  exact not_nativeUniformRawSubexponentialCeiling_of_rawDissipationTop
    hData hRawTop

/-- The uniform raw dissipation ceiling already yields a smooth
continuation, without an envelope assumption. -/
theorem smoothContinuationExtension_of_nativeUniformRawSubexponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b T) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  exact (not_nativeUniformRawSubexponentialCeiling_of_noH3PathExtension
    hH3 hNoExtension hClass hb) hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
