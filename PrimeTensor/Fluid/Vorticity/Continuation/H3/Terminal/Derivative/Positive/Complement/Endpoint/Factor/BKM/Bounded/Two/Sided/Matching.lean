import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Forced.Sign.Separation

/-!
# Two-sided matching in the bounded complement branch

The bounded complementary logarithm already yields ratio-one matching of
the selected gradient to the correctly signed curl. Both native logs are
positive in the cancellation regime, so the reverse ratio also tends to
one and both normalized additive gaps vanish on the original sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A ratio-one limit for two positive real sequences gives reciprocal
matching and vanishing normalized differences in both orientations. -/
theorem two_sided_matching_of_positive_ratio_one
    (A B : ℕ → ℝ)
    (hAPos : ∀ n : ℕ, 0 < A n)
    (hBPos : ∀ n : ℕ, 0 < B n)
    (hRatio : Tendsto (fun n : ℕ => A n / B n) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun n : ℕ => B n / A n) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (fun n : ℕ => (A n - B n) / B n)
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n : ℕ => (B n - A n) / A n)
        atTop (𝓝 (0 : ℝ)) := by
  have hInv :
      Tendsto (fun n : ℕ => (A n / B n)⁻¹)
        atTop (𝓝 ((1 : ℝ)⁻¹)) :=
    hRatio.inv₀ (by norm_num)
  have hReverse :
      Tendsto (fun n : ℕ => B n / A n) atTop (𝓝 (1 : ℝ)) := by
    have hFunction :
        (fun n : ℕ => B n / A n) =
          (fun n : ℕ => (A n / B n)⁻¹) := by
      funext n
      simp only [inv_div]
    rw [hFunction]
    simpa using hInv
  have hGapFunction :
      (fun n : ℕ => (A n - B n) / B n) =
        (fun n : ℕ => A n / B n - 1) := by
    funext n
    field_simp [ne_of_gt (hBPos n)] <;> ring
  have hReverseGapFunction :
      (fun n : ℕ => (B n - A n) / A n) =
        (fun n : ℕ => B n / A n - 1) := by
    funext n
    field_simp [ne_of_gt (hAPos n)] <;> ring
  refine ⟨hReverse, ?_, ?_⟩
  · rw [hGapFunction]
    simpa using hRatio.sub_const 1
  · rw [hReverseGapFunction]
    simpa using hReverse.sub_const 1

/-- The bounded complement branch retains its original bounded defect
and gains two-sided ratio matching and vanishing normalized gaps. -/
def H3TerminalEndpointBoundedComplementTwoSidedMatchingAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ) (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthBoundedComplementRatioAt
      u p sGradient τ y ∧
  Tendsto (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)) atTop (𝓝 (1 : ℝ)) ∧
  Tendsto (fun n : ℕ =>
      (h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n) -
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n)) /
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)) atTop (𝓝 (0 : ℝ)) ∧
  Tendsto (fun n : ℕ =>
      (h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n) -
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n)) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)) atTop (𝓝 (0 : ℝ))

/-- A cancellation-compatible bounded complement has two-sided matching
on its unchanged quantitative native sequence. -/
theorem positiveGrowth_boundedComplement_twoSidedMatching_of_data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hBounded :
      H3TerminalPositiveGrowthBoundedComplementRatioAt
        u p sGradient τ y) :
    H3TerminalEndpointBoundedComplementTwoSidedMatchingAt
      u p sGradient τ y := by
  obtain ⟨N, C, hAbs, hRatio⟩ := hBounded
  have hBounded' :
      H3TerminalPositiveGrowthBoundedComplementRatioAt
        u p sGradient τ y := ⟨N, C, hAbs, hRatio⟩
  have hGradientPos : ∀ n : ℕ,
      0 < h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n) := by
    intro n
    have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact lt_of_le_of_lt hnNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation n).1
  have hCurlPos : ∀ n : ℕ,
      0 < h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n) := by
    intro n
    have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact lt_of_le_of_lt hnNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation n).2
  have hRatio' : Tendsto (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)) atTop (𝓝 (1 : ℝ)) := by
    exact hRatio
  have hTwoSided := two_sided_matching_of_positive_ratio_one
    (fun n => h3TerminalOrientedSelectedGradientLogForPair
      u p sGradient (τ n) (y n))
    (fun n => h3TerminalOrientedSelectedSignedCurlLogForPair
      u p sGradient (τ n) (y n))
    hGradientPos hCurlPos hRatio'
  exact ⟨hBounded', hTwoSided.1, hTwoSided.2.1, hTwoSided.2.2⟩

/-- The sign-separated resolved alternative with both normalized-gap
limits included in its bounded complement branch. -/
def H3TerminalEndpointResolvedTwoSidedAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient τ y ∧
          ((H3TerminalComplementForcedRegime p sCurl sGradient ∧
              Tendsto (fun n : ℕ =>
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ n) (y n)) atTop atTop ∧
              Tendsto (fun n : ℕ =>
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ n) (y n)) atTop atBot) ∨
           (∃ sComplement : H3TerminalOrientation,
              H3TerminalPositiveGrowthTripleNativeCascade
                u b T p sCurl sGradient sComplement ∧
              H3TerminalEndpointTripleFiniteRateData
                u b T p sCurl sGradient sComplement) ∨
           (H3TerminalComplementCancellationRegime p sCurl sGradient ∧
              H3TerminalEndpointBoundedComplementTwoSidedMatchingAt
                u p sGradient τ y))

/-- Strengthen only the bounded branch of the resolved alternative. -/
theorem positiveGrowth_endpoint_resolvedTwoSided_of_signSeparated
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    (hResolved : H3TerminalEndpointResolvedSignSeparatedAlternative u b T) :
    H3TerminalEndpointResolvedTwoSidedAlternative u b T := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalEndpointResolvedTwoSidedAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hTriple | hBounded
  · exact Or.inl hForced
  · exact Or.inr (Or.inl hTriple)
  · exact Or.inr (Or.inr ⟨hBounded.1,
      positiveGrowth_boundedComplement_twoSidedMatching_of_data
        hData hBounded.1 hBounded.2⟩)

/-- Hypothetical nonextension yields the three fully resolved endpoint
branches on every strict terminal subtail. -/
theorem positiveGrowth_endpoint_resolvedTwoSided_on_every_subtail_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedTwoSidedAlternative u b T := by
  intro b hb
  exact positiveGrowth_endpoint_resolvedTwoSided_of_signSeparated
    (positiveGrowth_endpoint_resolvedSignSeparated_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb)

/-- Neutral continuation formulation with two-sided matching in the
bounded complement branch on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_endpoint_resolvedTwoSided_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedTwoSidedAlternative u b T) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_endpoint_resolvedTwoSided_on_every_subtail_of_noExtension
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
