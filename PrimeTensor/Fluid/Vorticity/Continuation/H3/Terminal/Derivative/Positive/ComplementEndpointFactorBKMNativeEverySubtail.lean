import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSubtail

/-!
# A quantitative native cascade on every strict terminal subtail

The corrected subtail extraction applies at any intermediate time `b`
between the energy-class start and the terminal endpoint. Consequently,
a path either has a smooth continuation or admits a complete quantitative
native positive-growth cascade on each such subtail. The cascade can vary
with `b`; no uniform choice is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Hypothetical nonextension supplies native quantitative data separately
on every strict subtail of the energy class. -/
theorem positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y := by
  intro b hb
  exact exists_terminal_positiveGrowth_quantitativeNativeData_on_subtail
    hH3 hNoExtension hClass hb

/-- Neutral alternative: smooth extension, or native quantitative
positive-growth data on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_quantitativeNativeData_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
