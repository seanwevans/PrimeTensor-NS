import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Matching.Scale

/-!
# Synchronized additive dominance and relative-rate outcomes

The triple native cascade supplies an indexed additive gap and a quantitative
positive-growth witness. The relative-rate extraction can be carried out
using that exact witness. This records additive dominance and the three
possible relative-rate subsequence outcomes together, so the indexed gap
bound remains available when studying a matching subsequence.

No relative-rate branch is selected unconditionally.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An additive gap above the index and a diverging smaller term give the
exact positive relative-gap identity on a terminal tail. -/
private theorem positive_relative_gap_of_additive
    (W L : ℕ → ℝ)
    (hLTop : Tendsto L atTop atTop)
    (hGap : ∀ n : ℕ, (n : ℝ) < W n - L n) :
    ∀ᶠ n : ℕ in atTop,
      0 < L n
        ∧
      0 < (W n - L n) / L n
        ∧
      W n / L n = 1 + (W n - L n) / L n := by
  have hLPos : ∀ᶠ n : ℕ in atTop, 0 < L n :=
    hLTop.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hLPos] with n hn
  have hGapPos : 0 < W n - L n := by
    have hIndex : (0 : ℝ) ≤ n := by positivity
    exact lt_of_le_of_lt hIndex (hGap n)
  refine ⟨hn, div_pos hGapPos hn, ?_⟩
  field_simp [ne_of_gt hn] <;> ring

/-- On a specified positive-growth witness, cancellation and additive
dominance yield the earlier relative-gap proposition without changing the
time or point sequence. -/
theorem positiveGrowth_relativeGapAt_of_dominanceData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime
        p sCurl sGradient)
    (hDominance :
      H3TerminalPositiveGrowthComplementDominanceAt
        u p sGradient sComplement τ y) :
    H3TerminalPositiveGrowthRelativeGapAt
      u p sGradient sComplement τ y := by
  have hGradientEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeGradientForPair u p (τ n) (y n))
        sGradient := by
    rcases hData with ⟨_, _, _, _, _, _, _, hGradientEscape, _⟩
    exact hGradientEscape
  have hCurlEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeCurlForPair u p (τ n) (y n))
        sCurl := by
    rcases hData with ⟨_, _, _, _, _, _, hCurlEscape, _, _⟩
    exact hCurlEscape
  have hATop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop :=
    orientedLog_tendsto_atTop_of_nativeDirectionalEscape
      hGradientEscape
  have hBTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop :=
    oriented_selectedSignedNativeCurlLog_tendsto_atTop_of_cancellation
      hCancellation hCurlEscape
  unfold H3TerminalPositiveGrowthRelativeGapAt
  refine ⟨hATop, hBTop, ?_⟩
  rcases hDominance with ⟨hSame, hGap, _⟩ | ⟨hOpp, hGap, _⟩
  · exact Or.inl ⟨hSame,
      positive_relative_gap_of_additive
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
        hBTop hGap⟩
  · exact Or.inr ⟨hOpp,
      positive_relative_gap_of_additive
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
        hATop hGap⟩

/-- The additive dominance and exact relative-gap data share one original
witness, whose rate subsequences inherit the quantitative cascade. -/
def H3TerminalPositiveGrowthDominanceRateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthComplementDominanceAt
      u p sGradient sComplement τ y
    ∧
  H3TerminalPositiveGrowthRelativeGapAt
      u p sGradient sComplement τ y
    ∧
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient
      ∧
      H3TerminalPositiveGrowthRelativeRateTrichotomyLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (A n - B n) / B n)
          (fun n : ℕ => A n / B n)
          (fun n : ℕ => B n / A n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeRateTrichotomyLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (B n - A n) / A n)
          (fun n : ℕ => B n / A n)
          (fun n : ℕ => A n / B n)))

/-- One triple native witness supports both indexed additive dominance and
all three neutral relative-rate outcomes. -/
theorem positiveGrowth_dominanceRate_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    ∃ τ : ℕ → ℝ,
      ∃ y : ℕ → Point3,
        H3TerminalPositiveGrowthQuantitativeNativeData
            u a T p sCurl sGradient τ y
          ∧
        H3TerminalComplementCancellationRegime
            p sCurl sGradient
          ∧
        H3TerminalPositiveGrowthDominanceRateAt
            u a T p sCurl sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hDominance⟩ :=
    positiveGrowth_complementDominance_of_tripleNativeCascade hTriple
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y :=
    positiveGrowth_relativeGapAt_of_dominanceData
      hData hCancellation hDominance
  refine ⟨τ, y, hData, hCancellation, hDominance, hRelative, ?_⟩
  dsimp only
  obtain ⟨_hATop, _hBTop, hBranches⟩ := hRelative
  rcases hBranches with ⟨hSame, hTail⟩ | ⟨hOpp, hTail⟩
  · refine Or.inl ⟨hSame, ?_⟩
    let gap : ℕ → ℝ := fun n =>
      (h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)
        - h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)) /
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)
    let ratio : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)
    let reciprocal : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)
    have hPos : ∀ᶠ n : ℕ in atTop, 0 ≤ gap n := by
      filter_upwards [hTail] with n hn
      exact le_of_lt hn.2.1
    have hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n := by
      filter_upwards [hTail] with n hn
      exact hn.2.2
    have hAlt := relativeTailAlternative_of_eventually_ratio_identity
      gap ratio hEq
    have hLift := positiveGrowth_relativeTailLift_of_alternative
      hData hAlt
    have hReciprocal : ∀ n : ℕ, reciprocal n = (ratio n)⁻¹ := by
      intro n
      simp only [reciprocal, ratio, inv_div]
    have hRecipLift := positiveGrowth_relativeReciprocalLift_of_tailLift
      hLift hReciprocal
    have hCluster := positiveGrowth_relativeClusterLift_of_reciprocalLift
      hData hPos hEq hRecipLift
    exact positiveGrowth_relativeRateTrichotomyLift_of_clusterLift
      hCluster hReciprocal
  · refine Or.inr ⟨hOpp, ?_⟩
    let gap : ℕ → ℝ := fun n =>
      (h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)
        - h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)
    let ratio : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)
    let reciprocal : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n) /
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)
    have hPos : ∀ᶠ n : ℕ in atTop, 0 ≤ gap n := by
      filter_upwards [hTail] with n hn
      exact le_of_lt hn.2.1
    have hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n := by
      filter_upwards [hTail] with n hn
      exact hn.2.2
    have hAlt := relativeTailAlternative_of_eventually_ratio_identity
      gap ratio hEq
    have hLift := positiveGrowth_relativeTailLift_of_alternative
      hData hAlt
    have hReciprocal : ∀ n : ℕ, reciprocal n = (ratio n)⁻¹ := by
      intro n
      simp only [reciprocal, ratio, inv_div]
    have hRecipLift := positiveGrowth_relativeReciprocalLift_of_tailLift
      hLift hReciprocal
    have hCluster := positiveGrowth_relativeClusterLift_of_reciprocalLift
      hData hPos hEq hRecipLift
    exact positiveGrowth_relativeRateTrichotomyLift_of_clusterLift
      hCluster hReciprocal

end

end Euclidean
end Bridge
end PrimeTensor
