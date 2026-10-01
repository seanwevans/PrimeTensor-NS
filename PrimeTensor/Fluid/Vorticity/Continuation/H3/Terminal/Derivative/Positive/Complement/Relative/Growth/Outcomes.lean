import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Escape.Counter.Superlinear

/-!
# Growth outcomes on one synchronized positive-growth witness

The existing relative-rate trichotomy is supplemented with direct growth
rules on its original witness. Matching gives both logs every linear bound
against the original selected index. A positive finite gap gives both logs
a linear lower scale there. Relative escape gives the dominant log every
linear bound against the extracted counter. No branch is selected here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Direct growth consequences for the matching, positive finite-rate,
and relative-escape subsequences of two oriented logarithms. -/
def H3TerminalPositiveGrowthOrientedGrowthRules
    (A B gap ratio dominant : ℕ → ℝ) : Prop :=
  (∀ (k : ℕ → ℕ) (M : ℝ),
    StrictMono k →
    Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 (0 : ℝ)) →
    0 < M →
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) < A (k n)
        ∧
      M * (k n : ℝ) < B (k n))
    ∧
  (∀ (c ε : ℝ) (k : ℕ → ℕ),
    0 < c →
    StrictMono k →
    Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c) →
    0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) < (c + ε) * A (k n)
        ∧
      (k n : ℝ) < (c + ε) * B (k n))
    ∧
  (∀ (k : ℕ → ℕ) (M : ℝ),
    Tendsto k atTop atTop →
    (∀ n : ℕ, (n : ℝ) + 1 < ratio (k n)) →
    0 < M →
    ∀ᶠ n : ℕ in atTop,
      M * ((n : ℝ) + 1) < dominant (k n))

/-- Direct branch growth rules and the relative-rate trichotomy are
attached to exactly the same additive-dominance time and point sequence. -/
def H3TerminalPositiveGrowthRelativeGrowthOutcomesAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthDominanceScaleClassificationAt
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
      H3TerminalPositiveGrowthOrientedGrowthRules
        A B (fun n : ℕ => (A n - B n) / B n)
        (fun n : ℕ => A n / B n) A)
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthOrientedGrowthRules
        A B (fun n : ℕ => (B n - A n) / A n)
        (fun n : ℕ => B n / A n) B))

/-- All three direct growth rules follow from the synchronized scale
classification on a specified witness. -/
theorem positiveGrowth_relativeGrowthOutcomes_of_scaleClassification
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hScale :
      H3TerminalPositiveGrowthDominanceScaleClassificationAt
        u a T p sCurl sGradient sComplement τ y) :
    H3TerminalPositiveGrowthRelativeGrowthOutcomesAt
      u a T p sCurl sGradient sComplement τ y := by
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y := hScale.1.1.2.1
  refine ⟨hScale, ?_⟩
  rcases hScale.2 with ⟨hSame, _⟩ | ⟨hOpp, _⟩
  · refine Or.inl ⟨hSame, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k M hk hMatching hM
      exact positiveGrowth_gradientMatching_forces_bothLogsSuperlinear
        hScale.1 hSame hk hMatching M hM
    · intro c ε k hc hk hFinite hε
      exact positiveGrowth_gradientFiniteRate_forces_bothLogsLinear
        hScale hSame hk hc hFinite hε
    · intro k M hkTop hRatio hM
      exact positiveGrowth_gradientRatioEscape_forces_everyCounterMultiple
        hRelative hkTop hRatio M hM
  · refine Or.inr ⟨hOpp, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro k M hk hMatching hM
      exact positiveGrowth_curlMatching_forces_bothLogsSuperlinear
        hScale.1 hOpp hk hMatching M hM
    · intro c ε k hc hk hFinite hε
      exact positiveGrowth_curlFiniteRate_forces_bothLogsLinear
        hScale hOpp hk hc hFinite hε
    · intro k M hkTop hRatio hM
      exact positiveGrowth_curlRatioEscape_forces_everyCounterMultiple
        hRelative hkTop hRatio M hM

/-- A triple native cascade has one quantitative witness carrying the
rate trichotomy and all of its direct growth consequences. -/
theorem positiveGrowth_relativeGrowthOutcomes_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeGrowthOutcomesAt
            u a T p sCurl sGradient sComplement τ y := by
  obtain ⟨τ, y, hData, hCancellation, hScale⟩ :=
    positiveGrowth_scaleClassification_of_tripleNativeCascade hTriple
  exact ⟨τ, y, hData, hCancellation,
    positiveGrowth_relativeGrowthOutcomes_of_scaleClassification hScale⟩

end

end Euclidean
end Bridge
end PrimeTensor
