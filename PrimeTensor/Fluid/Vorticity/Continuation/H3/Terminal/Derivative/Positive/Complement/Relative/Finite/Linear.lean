import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Resolved.Relative.Scale.Cascade

/-!
# Linear lower scale of the smaller oriented logarithm

At a finite normalized-gap cluster `c`, the synchronized scale rules give
`index / smallerLog < c + ε` eventually. Since the smaller log is positive
on a terminal tail, this is an explicit linear lower bound on that log.
Both positive-growth orientations retain their original time and point
witness; the finite cluster is a conditional subsequence outcome.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Convert a finite relative-rate scale rule into an eventual linear
lower bound for the smaller quantity on the same index subsequence. -/
theorem positiveGrowth_finiteScaleRule_forces_linearSmaller
    {gap ratio reciprocal smaller : ℕ → ℝ}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hRules :
      H3TerminalPositiveGrowthRelativeScaleRules
        gap ratio reciprocal smaller)
    (hk : StrictMono k)
    (hFinite : Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c))
    (hε : 0 < ε)
    (hSmallerPos :
      ∀ᶠ n : ℕ in atTop, 0 < smaller (k n)) :
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) < (c + ε) * smaller (k n) := by
  have hQuotient := hRules.1 c ε k hk hFinite hε
  filter_upwards [hSmallerPos, hQuotient] with n hn hBound
  exact (div_lt_iff₀ hn).1 hBound

/-- In the gradient-dominant finite-rate branch, the signed curl log
dominates the original subsequence index at the stated linear scale. -/
theorem positiveGrowth_gradientFiniteRate_forces_linearSignedCurl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hScale :
      H3TerminalPositiveGrowthDominanceScaleClassificationAt
        u a T p sCurl sGradient sComplement τ y)
    (hSame : sComplement = sGradient)
    (hk : StrictMono k)
    (hFinite :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 c))
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) <
        (c + ε) *
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) := by
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y := hScale.1.1.2.1
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.2.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hScale.2 with ⟨_, hRules⟩ | ⟨hOpp, _⟩
  · exact positiveGrowth_finiteScaleRule_forces_linearSmaller
      hRules hk hFinite hε hBPos
  · exact (hOpp hSame).elim

/-- In the curl-dominant finite-rate branch, the selected gradient log
dominates the original subsequence index at the stated linear scale. -/
theorem positiveGrowth_curlFiniteRate_forces_linearGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hScale :
      H3TerminalPositiveGrowthDominanceScaleClassificationAt
        u a T p sCurl sGradient sComplement τ y)
    (hOpp : sComplement ≠ sGradient)
    (hk : StrictMono k)
    (hFinite :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 c))
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) <
        (c + ε) *
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) := by
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y := hScale.1.1.2.1
  have hAPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hScale.2 with ⟨hSame, _⟩ | ⟨_, hRules⟩
  · exact (hOpp hSame).elim
  · exact positiveGrowth_finiteScaleRule_forces_linearSmaller
      hRules hk hFinite hε hAPos

end

end Euclidean
end Bridge
end PrimeTensor
