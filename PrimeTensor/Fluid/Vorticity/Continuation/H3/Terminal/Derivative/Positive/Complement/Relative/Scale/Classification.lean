import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Sublinear.Escape

/-!
# Scale rules on the synchronized relative-rate witness

The synchronized positive-growth witness retains its relative-rate
trichotomy and the matching smaller-log conclusion. A finite normalized
gap `c` bounds the index-to-smaller quotient by `c + ε` on each selected
subsequence. If that index quotient instead diverges, the normalized gap
and dominant ratio diverge and the reciprocal tends to zero on the same
subsequence. These implications do not select a relative-rate outcome.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Quantitative scale implications for finite relative clusters and for
diverging index-to-smaller quotients on one fixed witness. -/
def H3TerminalPositiveGrowthRelativeScaleRules
    (gap ratio reciprocal smaller : ℕ → ℝ) : Prop :=
  (∀ (c ε : ℝ) (k : ℕ → ℕ),
    StrictMono k →
    Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c) →
    0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) / smaller (k n) < c + ε)
    ∧
  (∀ k : ℕ → ℕ,
    StrictMono k →
    Tendsto (fun n : ℕ => (k n : ℝ) / smaller (k n)) atTop atTop →
    Tendsto (fun n : ℕ => gap (k n)) atTop atTop
      ∧
    Tendsto (fun n : ℕ => ratio (k n)) atTop atTop
      ∧
    Tendsto (fun n : ℕ => reciprocal (k n)) atTop (𝓝 (0 : ℝ)))

/-- Matching, finite-gap, and divergent-index scale rules attached to
the original additive-dominance and relative-rate witness. -/
def H3TerminalPositiveGrowthDominanceScaleClassificationAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthDominanceMatchingScaleAt
      u a T p sCurl sGradient sComplement τ y
    ∧
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient
      ∧
      H3TerminalPositiveGrowthRelativeScaleRules
        (fun n : ℕ => (A n - B n) / B n)
        (fun n : ℕ => A n / B n)
        (fun n : ℕ => B n / A n) B)
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeScaleRules
        (fun n : ℕ => (B n - A n) / A n)
        (fun n : ℕ => B n / A n)
        (fun n : ℕ => A n / B n) A))

/-- All scale rules follow from the indexed additive dominance and the
relative-gap data already present on the matching-scale witness. -/
theorem positiveGrowth_scaleClassification_of_matchingScale
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hMatching :
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
        u a T p sCurl sGradient sComplement τ y) :
    H3TerminalPositiveGrowthDominanceScaleClassificationAt
      u a T p sCurl sGradient sComplement τ y := by
  have hDominance := hMatching.1.1
  have hRelative := hMatching.1.2.1
  have hOrientation := hMatching.2
  refine ⟨hMatching, ?_⟩
  rcases hOrientation with ⟨hSame, _⟩ | ⟨hOpp, _⟩
  · refine Or.inl ⟨hSame, ?_⟩
    refine ⟨?_, ?_⟩
    · intro c ε k hk hFinite hε
      exact positiveGrowth_gradientFiniteGap_bounds_indexOverSignedCurl
        hDominance hRelative hSame hk hFinite hε
    · intro k hk hIndexTop
      exact positiveGrowth_gradientIndexOverSignedCurl_forces_relativeEscape
        hDominance hRelative hSame hk hIndexTop
  · refine Or.inr ⟨hOpp, ?_⟩
    refine ⟨?_, ?_⟩
    · intro c ε k hk hFinite hε
      exact positiveGrowth_curlFiniteGap_bounds_indexOverGradient
        hDominance hRelative hOpp hk hFinite hε
    · intro k hk hIndexTop
      exact positiveGrowth_curlIndexOverGradient_forces_relativeEscape
        hDominance hRelative hOpp hk hIndexTop

/-- The triple native cascade has a single quantitative witness for all
three neutral relative-rate outcomes and their scale implications. -/
theorem positiveGrowth_scaleClassification_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthDominanceScaleClassificationAt
            u a T p sCurl sGradient sComplement τ y := by
  obtain ⟨τ, y, hData, hCancellation, hMatching⟩ :=
    positiveGrowth_dominanceMatchingScale_of_tripleNativeCascade hTriple
  exact ⟨τ, y, hData, hCancellation,
    positiveGrowth_scaleClassification_of_matchingScale hMatching⟩

end

end Euclidean
end Bridge
end PrimeTensor
