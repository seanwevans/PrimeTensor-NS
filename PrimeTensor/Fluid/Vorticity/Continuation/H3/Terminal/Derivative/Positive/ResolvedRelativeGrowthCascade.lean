import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ResolvedRelativeScaleCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeGrowthOutcomes

/-!
# Relative growth outcomes in the terminal continuation alternative

The triple native branch has a synchronized witness for additive dominance,
relative-rate outcomes, and the three direct growth rules on their
selected subsequences.
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

/-- Triple native escape with the relative-growth classification attached to
its synchronized additive and relative-rate witness. -/
def H3TerminalPositiveGrowthRelativeGrowthTripleResolved
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
      H3TerminalPositiveGrowthRelativeGrowthOutcomesAt
          u a T p sCurl sGradient sComplement τ y

theorem positiveGrowth_relativeGrowthTripleResolved_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    H3TerminalPositiveGrowthRelativeGrowthTripleResolved
      u a T p sCurl sGradient sComplement := by
  exact ⟨hTriple,
    positiveGrowth_relativeGrowthOutcomes_of_tripleNativeCascade hTriple⟩

/-- The established terminal alternatives, with the synchronized
relative-growth classification in the triple native branch. -/
def H3TerminalPositiveGrowthResolvedRelativeGrowthAlternative
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
              H3TerminalPositiveGrowthRelativeGrowthTripleResolved
                u a T p sCurl sGradient sComplement)
            ∨
            (H3TerminalComplementCancellationRegime
                p sCurl sGradient
              ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine only the triple native branch of the resolved scale
alternative, keeping the original outer witness. -/
theorem positiveGrowth_resolvedRelativeGrowth_of_resolvedRelativeScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hResolved :
      H3TerminalPositiveGrowthResolvedRelativeScaleAlternative u a T) :
    H3TerminalPositiveGrowthResolvedRelativeGrowthAlternative u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalPositiveGrowthResolvedRelativeGrowthAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hOther
  · exact Or.inl hForced
  · rcases hOther with ⟨sComplement, hTripleResolved⟩ | hBounded
    · exact Or.inr (Or.inl
        ⟨sComplement,
          positiveGrowth_relativeGrowthTripleResolved_of_tripleNativeCascade
            hTripleResolved.1⟩)
    · exact Or.inr (Or.inr hBounded)

/-- If smooth continuation fails, the triple native branch of the neutral
terminal alternative satisfies the matching, finite-gap, and escape growth rules. -/
theorem positiveGrowth_resolvedRelativeGrowth_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthResolvedRelativeGrowthAlternative u a T :=
  positiveGrowth_resolvedRelativeGrowth_of_resolvedRelativeScale
    (positiveGrowth_resolvedRelativeScale_of_noH3PathExtension
      hH3 hNoExtension hClass hb)

/-- Smooth continuation or the resolved neutral relative-growth alternative. -/
theorem smoothContinuationExtension_or_positiveGrowth_resolvedRelativeGrowth
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthResolvedRelativeGrowthAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_resolvedRelativeGrowth_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
