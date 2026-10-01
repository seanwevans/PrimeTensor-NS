import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Uniform.Ceiling.Continuation

/-!
# Indexed rates and the physical endpoint clock

An arbitrary prescribed rate in the new sequence index can be attained
by cofinally reindexing a quantitative native witness on which raw
dissipation diverges. An upper bound evaluated at the actual time,
however, retains its original argument under reindexing. The latter is
the appropriate interface for an endpoint clock assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A divergent raw dissipation sequence can be reindexed above any
finite rate prescribed at the new index, while retaining all native
quantitative data. -/
theorem quantitativeNative_rawDissipation_above_any_indexRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawTop : Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop)
    (R : ℕ → ℝ) :
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ, n ≤ k n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      (∀ n : ℕ, R n < velocityH3DissipationAt u (τ (k n))) := by
  classical
  have hPick : ∀ n : ℕ, ∃ j : ℕ,
      n ≤ j ∧ R n < velocityH3DissipationAt u (τ j) := by
    intro n
    have hLarge : ∀ᶠ j : ℕ in atTop,
        R n < velocityH3DissipationAt u (τ j) :=
      hRawTop.eventually (eventually_gt_atTop (R n))
    obtain ⟨j, hjIndex, hjLarge⟩ :=
      ((eventually_ge_atTop n).and hLarge).exists
    exact ⟨j, hjIndex, hjLarge⟩
  choose k hk using hPick
  have hCofinal : ∀ n : ℕ, n ≤ k n := fun n => (hk n).1
  exact ⟨k, hCofinal,
    positiveGrowth_quantitativeNativeData_comp_cofinal hData hCofinal,
    fun n => (hk n).2⟩

/-- Hypothetical nonextension gives a quantitative native witness
whose raw dissipation exceeds any chosen index rate at every index. -/
theorem positiveGrowth_native_rawDissipation_above_any_indexRate_on_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (R : ℕ → ℝ) :
    ∃ p : H3TerminalCurlGradientPair,
      ∃ sCurl sGradient : H3TerminalOrientation,
        ∃ τ : ℕ → ℝ,
          ∃ y : ℕ → Point3,
            H3TerminalPositiveGrowthQuantitativeNativeData
              u b T p sCurl sGradient τ y ∧
            (∀ n : ℕ, R n < velocityH3DissipationAt u (τ n)) := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
      hH3 hNoExtension hClass hb
  have hTauLT : Tendsto τ atTop (𝓝[<] T) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hData.2.1,
        Eventually.of_forall (fun n => (hData.1 n).1.2)⟩
  have hRawTop : Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop :=
    (velocityH3DissipationAt_tendsto_atTop_nhdsLT_of_noH3PathExtension
      hH3 hNoExtension hClass).comp hTauLT
  obtain ⟨k, _, hReindexed, hRate⟩ :=
    quantitativeNative_rawDissipation_above_any_indexRate
      hData hRawTop R
  exact ⟨p, sCurl, sGradient,
    (fun n => τ (k n)), (fun n => y (k n)), hReindexed, hRate⟩

/-- A raw dissipation bound expressed using the physical time remaining
to the endpoint. Its argument is independent of a witness's numbering. -/
def H3TerminalPhysicalRawDissipationCeiling
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Ioo b T →
    velocityH3DissipationAt u t ≤ F (T - t)

/-- The physical clock ceiling holds at any reindexed time, with the
same physical clock argument. No growth restriction on the index map
is needed. -/
theorem physicalRawDissipationCeiling_on_reindexedNative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ} {F : ℝ → ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hCeiling : H3TerminalPhysicalRawDissipationCeiling u b T F)
    (k : ℕ → ℕ) :
    ∀ n : ℕ,
      velocityH3DissipationAt u (τ (k n)) ≤ F (T - τ (k n)) := by
  intro n
  exact hCeiling (τ (k n)) (hData.1 (k n)).1

/-- If raw dissipation diverges on a native witness, every physical
upper clock for it must diverge along the same times. -/
theorem physicalRawDissipationCeiling_clockTop_on_native
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ} {F : ℝ → ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawTop : Tendsto
      (fun n : ℕ => velocityH3DissipationAt u (τ n)) atTop atTop)
    (hCeiling : H3TerminalPhysicalRawDissipationCeiling u b T F) :
    Tendsto (fun n : ℕ => F (T - τ n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [hRawTop.eventually (eventually_ge_atTop M)] with n hn
  exact hn.trans (hCeiling (τ n) (hData.1 n).1)

end

end Euclidean
end Bridge
end PrimeTensor
