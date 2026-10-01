import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Resolved.Relative.Rate.Cascade
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Scale forced by relative matching and additive complement escape

The complementary logarithm exceeds the index in the triple native
cascade. If the dominant and smaller oriented logarithms match in ratio
along a cofinal subsequence, their normalized additive gap tends to zero.
The index divided by the smaller logarithm must then tend to zero too.

This is a quantitative condition on the matching branch. The statement
applies to a common witness carrying additive dominance and relative gap
data; it does not assert that matching occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Squeeze an indexed lower bound on a gap by its vanishing quotient with a
positive denominator. -/
private theorem index_div_tendsto_zero_of_gap_ratio_zero
    (i : ℕ → ℕ)
    (G D : ℕ → ℝ)
    (hIndex : ∀ n : ℕ, (i n : ℝ) < G n)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hGapZero :
      Tendsto (fun n : ℕ => G n / D n) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n : ℕ => (i n : ℝ) / D n)
      atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' ?_ ?_ hGapZero
  · filter_upwards [hDPos] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hn)
  · filter_upwards [hDPos] with n hn
    exact (div_le_div_iff_of_pos_right hn).2 (hIndex n).le

/-- In the gradient-dominant matching branch, the signed curl logarithm
outgrows the original index along the matching subsequence. -/
theorem positiveGrowth_gradientMatching_forces_superlinearSignedCurl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hDominance :
      H3TerminalPositiveGrowthComplementDominanceAt
        u p sGradient sComplement τ y)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
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
        atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n : ℕ =>
        (k n : ℝ) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      atTop (𝓝 (0 : ℝ)) := by
  have hBTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop := hRelative.2.1
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hBTop.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨_, hGap, _⟩ | ⟨hOpp, _, _⟩
  · exact index_div_tendsto_zero_of_gap_ratio_zero
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n))
          - h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n => hGap (k n)) hBPos hMatching
  · exact (hOpp hSame).elim

/-- In the curl-dominant matching branch, the oriented selected gradient
logarithm outgrows the original index along the matching subsequence. -/
theorem positiveGrowth_curlMatching_forces_superlinearGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hDominance :
      H3TerminalPositiveGrowthComplementDominanceAt
        u p sGradient sComplement τ y)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
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
        atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n : ℕ =>
        (k n : ℝ) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      atTop (𝓝 (0 : ℝ)) := by
  have hATop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop := hRelative.1
  have hAPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hATop.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨hSame, _, _⟩ | ⟨_, hGap, _⟩
  · exact (hOpp hSame).elim
  · exact index_div_tendsto_zero_of_gap_ratio_zero
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n))
          - h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n => hGap (k n)) hAPos hMatching

end

end Euclidean
end Bridge
end PrimeTensor
