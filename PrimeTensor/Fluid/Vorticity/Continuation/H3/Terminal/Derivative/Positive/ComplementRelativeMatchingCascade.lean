import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeSynchronizedCascade

/-!
# Matching scale on the synchronized positive-growth witness

Indexed additive dominance and the relative-rate trichotomy hold on the
same triple native witness. Along every matching subsequence, the smaller
oriented logarithm therefore outgrows the original subsequence index.
The finite positive-gap and cofinal escape outcomes remain available in
the synchronized rate classification.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Synchronized additive dominance and relative-rate classification,
including the forced scale on any matching subsequence. -/
def H3TerminalPositiveGrowthDominanceMatchingScaleAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthDominanceRateAt
      u a T p sCurl sGradient sComplement τ y
    ∧
  ((sComplement = sGradient
      ∧
      ∀ k : ℕ → ℕ,
        StrictMono k →
        Tendsto
            (fun n : ℕ =>
              (h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n))
                - h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n))) /
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (0 : ℝ)) →
        Tendsto
            (fun n : ℕ =>
              (k n : ℝ) /
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (0 : ℝ)))
    ∨
    (sComplement ≠ sGradient
      ∧
      ∀ k : ℕ → ℕ,
        StrictMono k →
        Tendsto
            (fun n : ℕ =>
              (h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n))
                - h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n))) /
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (0 : ℝ)) →
        Tendsto
            (fun n : ℕ =>
              (k n : ℝ) /
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (0 : ℝ))))

/-- Each matching subsequence of the synchronized witness has the
corresponding superlinear smaller logarithm. -/
theorem positiveGrowth_dominanceMatchingScale_of_dominanceRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hRate :
      H3TerminalPositiveGrowthDominanceRateAt
        u a T p sCurl sGradient sComplement τ y) :
    H3TerminalPositiveGrowthDominanceMatchingScaleAt
      u a T p sCurl sGradient sComplement τ y := by
  have hDom := hRate.1
  have hRel := hRate.2.1
  have hOrientation := hRate.2.2
  refine ⟨hRate, ?_⟩
  rcases hOrientation with ⟨hSame, _⟩ | ⟨hOpp, _⟩
  · exact Or.inl ⟨hSame, fun k hk hMatching =>
      positiveGrowth_gradientMatching_forces_superlinearSignedCurl
        hDom hRel hSame hk hMatching⟩
  · exact Or.inr ⟨hOpp, fun k hk hMatching =>
      positiveGrowth_curlMatching_forces_superlinearGradient
        hDom hRel hOpp hk hMatching⟩

/-- A triple native cascade has one witness carrying additive dominance,
all relative-rate outcomes, and the smaller-log scale on matching tails. -/
theorem positiveGrowth_dominanceMatchingScale_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthDominanceMatchingScaleAt
            u a T p sCurl sGradient sComplement τ y := by
  obtain ⟨τ, y, hData, hCancellation, hRate⟩ :=
    positiveGrowth_dominanceRate_of_tripleNativeCascade hTriple
  exact ⟨τ, y, hData, hCancellation,
    positiveGrowth_dominanceMatchingScale_of_dominanceRate hRate⟩

end

end Euclidean
end Bridge
end PrimeTensor
