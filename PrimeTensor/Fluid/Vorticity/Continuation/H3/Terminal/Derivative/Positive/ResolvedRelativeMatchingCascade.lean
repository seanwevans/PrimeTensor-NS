import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeMatchingCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ResolvedRelativeRateCascade

/-!
# Matching scale in the resolved terminal continuation alternative

The triple native branch has a synchronized witness for additive dominance,
relative-rate outcomes, and the forced scale of every matching subsequence.
This refinement carries that witness into the neutral terminal continuation
alternative while retaining the reinforcing-sign and bounded-complement
branches. It does not assert which terminal branch occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Triple native escape with the matching-scale conclusion attached to
its synchronized additive and relative-rate witness. -/
def H3TerminalPositiveGrowthDominanceMatchingScaleTripleResolved
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
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
          u a T p sCurl sGradient sComplement τ y

theorem positiveGrowth_dominanceMatchingScaleTripleResolved_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    H3TerminalPositiveGrowthDominanceMatchingScaleTripleResolved
      u a T p sCurl sGradient sComplement := by
  exact ⟨hTriple,
    positiveGrowth_dominanceMatchingScale_of_tripleNativeCascade hTriple⟩

/-- The established terminal alternatives, with the synchronized
matching-scale classification in the triple native branch. -/
def H3TerminalPositiveGrowthResolvedRelativeMatchingAlternative
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
              H3TerminalPositiveGrowthDominanceMatchingScaleTripleResolved
                u a T p sCurl sGradient sComplement)
            ∨
            (H3TerminalComplementCancellationRegime
                p sCurl sGradient
              ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine only the triple native branch of the resolved relative-rate
alternative, keeping the original outer witness. -/
theorem positiveGrowth_resolvedRelativeMatching_of_resolvedRelativeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hResolved :
      H3TerminalPositiveGrowthResolvedRelativeRateAlternative u a T) :
    H3TerminalPositiveGrowthResolvedRelativeMatchingAlternative u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalPositiveGrowthResolvedRelativeMatchingAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hOther
  · exact Or.inl hForced
  · rcases hOther with ⟨sComplement, hTripleResolved⟩ | hBounded
    · exact Or.inr (Or.inl
        ⟨sComplement,
          positiveGrowth_dominanceMatchingScaleTripleResolved_of_tripleNativeCascade
            hTripleResolved.1⟩)
    · exact Or.inr (Or.inr hBounded)

/-- If smooth continuation fails, the triple native branch of the neutral
terminal alternative satisfies the matching smaller-log scale condition. -/
theorem positiveGrowth_resolvedRelativeMatching_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthResolvedRelativeMatchingAlternative u a T :=
  positiveGrowth_resolvedRelativeMatching_of_resolvedRelativeRate
    (positiveGrowth_resolvedRelativeRate_of_noH3PathExtension
      hH3 hNoExtension hClass hb)

/-- Smooth continuation or the resolved neutral matching-scale alternative. -/
theorem smoothContinuationExtension_or_positiveGrowth_resolvedRelativeMatching
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthResolvedRelativeMatchingAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_resolvedRelativeMatching_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
