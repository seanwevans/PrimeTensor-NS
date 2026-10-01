import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Uniform.Vorticity.Ceiling.Continuation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Rate.Extraction

/-!
# Rate selection from one specified native witness

The indexed raw dissipation ceiling is imposed only on the supplied
quantitative native witness. Under hypothetical nonextension, an
eventual constant ceiling for its normalized vorticity factor would
force an exponential lower rate for raw dissipation on that same
witness, contradicting the supplied upper ceiling. The normalized
vorticity factor is therefore unbounded on the original witness and
admits a cofinal quantitative extraction.

The raw ceiling is not transferred to the extracted witness: its
index changes under that extraction. In particular, this statement
does not quantify an indexed ceiling over all reindexings.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An indexed raw dissipation ceiling on one fixed sequence of times. -/
def H3TerminalNativeRawSubexponentialCeilingOnWitness
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c →
    ∀ᶠ n : ℕ in atTop,
      velocityH3DissipationAt u (τ n) ≤
        Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2

/-- An upper raw dissipation rate on this witness excludes an
eventual constant ceiling for its own normalized vorticity factor. -/
theorem not_eventually_bounded_nativeVorticityRatio_of_selectedRawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {g : ℝ → ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ) :
    ¬ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C := by
  rintro ⟨C, hVorticityCeiling⟩
  exact
    (positiveGrowth_native_rawDissipation_not_subexponential_sqrt
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling)
      hRawCeiling

/-- Extract divergent normalized vorticity while preserving the full
quantitative native cascade. The denominator retains the original
index `k n`, and the raw ceiling remains attached to the original
witness. -/
theorem positiveGrowth_native_vorticityExtraction_of_selectedRawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a b T : ℝ} {g : ℝ → ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hRawCeiling : H3TerminalNativeRawSubexponentialCeilingOnWitness u τ) :
    ∃ k : ℕ → ℕ,
      (∀ n : ℕ, n ≤ k n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      (∀ n : ℕ,
        (n : ℝ) <
          (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1)) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |g (τ (k n))|) ^ 2 / ((k n : ℝ) + 1))
        atTop atTop := by
  obtain ⟨k, hk, hTop⟩ :=
    cofinal_extraction_of_no_eventual_real_ceiling
      (fun n : ℕ =>
        (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1))
      (not_eventually_bounded_nativeVorticityRatio_of_selectedRawCeiling
        hH3 hNoExtension hClass hb hg hData hRawCeiling)
  exact ⟨k, (fun n => (hk n).1),
    positiveGrowth_quantitativeNativeData_comp_cofinal
      hData (fun n => (hk n).1),
    (fun n => (hk n).2), hTop⟩

end

end Euclidean
end Bridge
end PrimeTensor
