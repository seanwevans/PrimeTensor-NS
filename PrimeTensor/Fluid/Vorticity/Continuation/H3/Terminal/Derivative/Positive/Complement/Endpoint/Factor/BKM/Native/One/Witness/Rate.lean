import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Reindexed.Rate

/-!
# One native witness for the endpoint rate alternative

The extracted vorticity branch already carries the complete native
cascade with its own index. It can therefore replace the original
witness. Both branches may be stated using one sequence of times and
points on each strict terminal subtail.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A native quantitative witness whose own index sees either a
divergent normalized vorticity factor or eventual exponential raw H³
dissipation growth. -/
def H3TerminalPositiveGrowthNativeRateAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient τ y ∧
          (((∀ n : ℕ,
              (n : ℝ) <
                (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1)) ∧
            Tendsto
              (fun n : ℕ =>
                (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1))
              atTop atTop) ∨
            (∃ c : ℝ, 0 < c ∧
              ∀ᶠ n : ℕ in atTop,
                Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
                  velocityH3DissipationAt u (τ n)))

/-- Hypothetical nonextension selects one native witness on every
strict subtail. The selected sequence carries whichever rate branch
holds, including the reindexed cascade in the vorticity branch. -/
theorem positiveGrowth_native_rateAlternative_oneWitness_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthNativeRateAlternative u b T g := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hRate⟩ :=
    positiveGrowth_native_reindexedVorticity_or_rawDissipation_on_every_subtail
      hH3 hNoExtension hClass hg b hb
  rcases hRate with ⟨k, _hk, hNative, hGrowth, hTop⟩ |
      ⟨c, hcPos, hDissipation⟩
  · exact ⟨p, sCurl, sGradient,
      (fun n => τ (k n)), (fun n => y (k n)),
      hNative, Or.inl ⟨hGrowth, hTop⟩⟩
  · exact ⟨p, sCurl, sGradient, τ, y,
      hData, Or.inr ⟨c, hcPos, hDissipation⟩⟩

/-- Neutral alternative: a smooth continuation or a single native
rate witness on each strict subtail. -/
theorem smoothContinuationExtension_or_native_rateOneWitness_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ} {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hg : ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalPositiveGrowthNativeRateAlternative u b T g) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_native_rateAlternative_oneWitness_on_every_subtail
        hH3 hExtension hClass hg)

end

end Euclidean
end Bridge
end PrimeTensor
