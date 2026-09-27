import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeMatchingSuperlinear

/-!
# Both oriented logarithms outgrow the index under relative matching

On a matching subsequence the smaller oriented log exceeds every fixed
positive multiple of the original index. Indexed additive dominance makes
the other oriented log strictly larger. Thus the same eventual bound holds
for both logs, regardless of which orientation supplies the complement.
The matching branch remains conditional.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A positive indexed additive gap transfers any eventual lower bound
from the smaller log to the dominant log on the same subsequence. -/
private theorem both_logs_above_index_multiple
    (W L : ℕ → ℝ)
    (k : ℕ → ℕ)
    (M : ℝ)
    (hGap : ∀ n : ℕ, (k n : ℝ) < W n - L n)
    (hSmaller :
      ∀ᶠ n : ℕ in atTop, M * (k n : ℝ) < L n) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) < L n
        ∧
      M * (k n : ℝ) < W n := by
  filter_upwards [hSmaller] with n hn
  have hIndexNonneg : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg _
  have hDominant : L n < W n := by
    linarith [hGap n]
  exact ⟨hn, hn.trans hDominant⟩

/-- Gradient-dominant matching makes the signed curl and selected gradient
logs both exceed every fixed positive multiple of the original index. -/
theorem positiveGrowth_gradientMatching_forces_bothLogsSuperlinear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hMatchingScale :
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
        u a T p sCurl sGradient sComplement τ y)
    (hSame : sComplement = sGradient)
    (hk : StrictMono k)
    (hMatching :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n))
        ∧
      M * (k n : ℝ) <
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) := by
  have hSmaller :=
    positiveGrowth_gradientMatching_forces_everyLinearSignedCurl
      hMatchingScale hSame hk hMatching M hM
  rcases hMatchingScale.1.1 with ⟨_, hGap, _⟩ | ⟨hOpp, _, _⟩
  · have hBoth := both_logs_above_index_multiple
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      k M (fun n => hGap (k n)) hSmaller
    filter_upwards [hBoth] with n hn
    exact ⟨hn.2, hn.1⟩
  · exact (hOpp hSame).elim

/-- Curl-dominant matching makes the selected gradient and signed curl
logs both exceed every fixed positive multiple of the original index. -/
theorem positiveGrowth_curlMatching_forces_bothLogsSuperlinear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hMatchingScale :
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
        u a T p sCurl sGradient sComplement τ y)
    (hOpp : sComplement ≠ sGradient)
    (hk : StrictMono k)
    (hMatching :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n))
        ∧
      M * (k n : ℝ) <
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) := by
  have hSmaller :=
    positiveGrowth_curlMatching_forces_everyLinearGradient
      hMatchingScale hOpp hk hMatching M hM
  rcases hMatchingScale.1.1 with ⟨hSame, _, _⟩ | ⟨_, hGap, _⟩
  · exact (hOpp hSame).elim
  · exact both_logs_above_index_multiple
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      k M (fun n => hGap (k n)) hSmaller

end

end Euclidean
end Bridge
end PrimeTensor
