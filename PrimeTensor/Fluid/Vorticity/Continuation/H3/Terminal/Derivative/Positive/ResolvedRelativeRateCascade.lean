import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeRateTrichotomy

/-!
# Relative-rate outcomes in the resolved terminal alternative

The terminal continuation alternative first separates reinforcing signs,
unbounded cancellation-compatible complement, and bounded complement.
Within the unbounded cancellation-compatible branch, the triple native
cascade now admits the three relative-rate subsequence outcomes: matching,
positive finite separation, or dominant ratio escape.

This module attaches those outcomes to the conditional nonextension result
while retaining the original positive-growth witness and the bounded
complement branch. It does not select any branch unconditionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Triple native escape together with the synchronized relative-rate
trichotomy that it entails. -/
def H3TerminalPositiveGrowthRelativeRateTripleResolved
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation) : Prop :=
  H3TerminalPositiveGrowthTripleNativeCascade
      u a T p sCurl sGradient sComplement
    ∧
  ∃ τ : ℕ → ℝ,
    ∃ y : ℕ → Point3,
      H3TerminalPositiveGrowthQuantitativeNativeData
          u a T p sCurl sGradient τ y
        ∧
      H3TerminalComplementCancellationRegime
          p sCurl sGradient
        ∧
      H3TerminalPositiveGrowthRelativeRateTrichotomyAt
          u a T p sCurl sGradient sComplement τ y

/-- Resolve the relative rates inside a given triple native branch. -/
theorem positiveGrowth_relativeRateTripleResolved_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    H3TerminalPositiveGrowthRelativeRateTripleResolved
      u a T p sCurl sGradient sComplement := by
  exact ⟨hTriple,
    positiveGrowth_relativeRateTrichotomy_of_tripleNativeCascade hTriple⟩

/-- The resolved terminal alternative with all three relative-rate
outcomes attached to the unbounded complementary branch. -/
def H3TerminalPositiveGrowthResolvedRelativeRateAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
              u a T p sCurl sGradient τ y
            ∧
          ((H3TerminalComplementForcedRegime p sCurl sGradient
              ∧
            (∀ n : ℕ,
              2 * (n : ℝ) <
                h3TerminalOrientedValue sGradient
                  (PrimeTensor.Bridge.MulReal.logValue
                    (h3TerminalNativeComplementGradientForPair
                      u p (τ n) (y n))))
              ∧
            H3TerminalNativeLogDirectionalEscape
              (fun n : ℕ =>
                h3TerminalNativeComplementGradientForPair
                  u p (τ n) (y n))
              sGradient)
            ∨
            (∃ sComplement : H3TerminalOrientation,
              H3TerminalPositiveGrowthRelativeRateTripleResolved
                u a T p sCurl sGradient sComplement)
            ∨
            (H3TerminalComplementCancellationRegime
                p sCurl sGradient
              ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine the triple branch of the established resolved complement
alternative without changing its outer positive-growth witness. -/
theorem positiveGrowth_resolvedRelativeRate_of_resolvedComplement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hResolved :
      H3TerminalPositiveGrowthResolvedComplementAlternative u a T) :
    H3TerminalPositiveGrowthResolvedRelativeRateAlternative u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalPositiveGrowthResolvedRelativeRateAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hOther
  · exact Or.inl hForced
  · rcases hOther with ⟨sComplement, hTriple⟩ | hBounded
    · exact Or.inr (Or.inl
        ⟨sComplement,
          positiveGrowth_relativeRateTripleResolved_of_tripleNativeCascade
            hTriple⟩)
    · exact Or.inr (Or.inr hBounded)

/-- Hypothetical failure of smooth continuation yields the full neutral
terminal alternative, including the relative-rate trichotomy if the
triple-escape branch is selected. -/
theorem positiveGrowth_resolvedRelativeRate_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthResolvedRelativeRateAlternative u a T :=
  positiveGrowth_resolvedRelativeRate_of_resolvedComplement
    (positiveGrowth_resolvedComplement_of_noH3PathExtension
      hH3 hNoExtension hClass hb)

/-- Neutral continuation or the resolved relative-rate alternative. -/
theorem smoothContinuationExtension_or_positiveGrowth_resolvedRelativeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthResolvedRelativeRateAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_resolvedRelativeRate_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
