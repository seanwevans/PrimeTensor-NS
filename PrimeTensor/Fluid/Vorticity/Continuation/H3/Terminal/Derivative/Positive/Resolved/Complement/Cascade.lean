import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Triple.Cascade

/-!
# Resolved complementary-gradient alternatives on the positive-growth cascade

The positive-growth native cascade has one fixed structural pair and fixed curl
and selected-gradient orientations.  Its complementary-gradient sign split is
resolved into three exhaustive conditional outcomes:

* reinforcing signs give a `2n` lower bound and directional complementary
  escape on the original positive-growth sequence;
* cancellation-compatible signs with a tail-unbounded complement give a
  cofinal reindexing with three directional native escapes and the full
  positive-growth scalar and frequency cascade;
* cancellation-compatible signs with an eventually bounded complement give
  a bounded additive defect and ratio-one matching on the original sequence.

The result is a neutral necessary alternative under hypothetical failure of
smooth continuation.  None of its branches is asserted to occur unconditionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Eventual bounded complementary logarithm and ratio-one matching on a
specified time and point sequence. -/
def H3TerminalPositiveGrowthBoundedComplementRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  ∃ N : ℕ,
    ∃ C : ℝ,
      (∀ n : ℕ,
        N ≤ n →
          abs
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeComplementGradientForPair
                u p (τ n) (y n))) ≤ C
            ∧
          abs
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeGradientForPair
                u p (τ n) (y n))
              - h3TerminalSelectedSignedNativeCurlLog
                  u p (τ n) (y n)) ≤ C)
        ∧
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedValue sGradient
              (PrimeTensor.Bridge.MulReal.logValue
                (h3TerminalNativeGradientForPair
                  u p (τ n) (y n))) /
            h3TerminalOrientedValue sGradient
              (h3TerminalSelectedSignedNativeCurlLog
                u p (τ n) (y n)))
        atTop (𝓝 1)

/-- Full positive-growth data together with one of the three complementary
terminal outcomes.  The inner triple-escape witness can use a cofinal
reindexing of the original `τ, y` witness. -/
def H3TerminalPositiveGrowthResolvedComplementAlternative
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
              H3TerminalPositiveGrowthTripleNativeCascade
                u a T p sCurl sGradient sComplement)
            ∨
            (H3TerminalComplementCancellationRegime
                p sCurl sGradient
              ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine the ratio alternative to the synchronized triple native cascade
or the bounded ratio-one branch while retaining the forced branch. -/
theorem positiveGrowth_resolvedComplement_of_ratioAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hAlternative :
      H3TerminalPositiveGrowthNativeComplementRatioAlternative
        u a T) :
    H3TerminalPositiveGrowthResolvedComplementAlternative
      u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ :=
    hAlternative
  unfold H3TerminalPositiveGrowthResolvedComplementAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hCancellationRatio
  · exact Or.inl hForced
  · obtain ⟨hCancellation, hRatioBranches⟩ :=
      hCancellationRatio
    rcases hRatioBranches with hUnbounded | hBounded
    · obtain ⟨sComplement, hCofinal⟩ := hUnbounded
      exact Or.inr (Or.inl
        ⟨sComplement,
          positiveGrowth_tripleNativeCascade_of_complementCofinal
            hData hCancellation hCofinal⟩)
    · exact Or.inr (Or.inr ⟨hCancellation, hBounded⟩)

/-- Hypothetical nonextension yields the exhaustive three-branch
positive-growth complementary alternative. -/
theorem positiveGrowth_resolvedComplement_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthResolvedComplementAlternative u a T :=
  positiveGrowth_resolvedComplement_of_ratioAlternative
    (positiveGrowth_nativeComplementRatioAlternative_of_noH3PathExtension
      hH3 hNoExtension hClass hb)

/-- Neutral continuation formulation of the resolved alternative. -/
theorem smoothContinuationExtension_or_positiveGrowth_resolvedComplement
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthResolvedComplementAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_resolvedComplement_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
