import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ResolvedRelativeGrowthCascade

/-!
# Promoting escape growth through controlled subsequence extraction

Relative escape forces the dominant oriented log above every multiple of
the extracted counter `n + 1`. If the selected original indices also obey
an eventual bound `k n ≤ C (n + 1)` for some positive `C`, that growth
promotes to every multiple of the original index `k n`. The established
cofinal extraction does not itself provide this additional bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A linear upper bound on the extraction map transfers a strict
dominant-log bound from the extracted counter to the original index. -/
private theorem original_index_bound_of_counter_bound
    (k : ℕ → ℕ)
    (W : ℕ → ℝ)
    (C M : ℝ)
    (hM : 0 < M)
    (hkBound :
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) ≤ C * ((n : ℝ) + 1))
    (hCounter :
      ∀ᶠ n : ℕ in atTop,
        (M * C) * ((n : ℝ) + 1) < W n) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) < W n := by
  filter_upwards [hkBound, hCounter] with n hn hW
  have hScaled :
      M * (k n : ℝ) ≤ (M * C) * ((n : ℝ) + 1) := by
    calc
      M * (k n : ℝ) ≤ M * (C * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hn hM.le
      _ = (M * C) * ((n : ℝ) + 1) := by ring
  exact hScaled.trans_lt hW

/-- With linearly controlled extraction, gradient-dominant escape forces
every original-index lower bound on the selected gradient log. -/
theorem positiveGrowth_gradientEscape_controlledExtraction_originalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {C : ℝ}
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (hC : 0 < C)
    (hkBound :
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) ≤ C * ((n : ℝ) + 1))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hCounter :=
    positiveGrowth_gradientRatioEscape_forces_everyCounterMultiple
      hRelative hkTop hRatio (M * C) (mul_pos hM hC)
  exact original_index_bound_of_counter_bound
    k
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    C M hM hkBound hCounter

/-- With linearly controlled extraction, curl-dominant escape forces
every original-index lower bound on the signed curl log. -/
theorem positiveGrowth_curlEscape_controlledExtraction_originalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {C : ℝ}
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (hC : 0 < C)
    (hkBound :
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) ≤ C * ((n : ℝ) + 1))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hCounter :=
    positiveGrowth_curlRatioEscape_forces_everyCounterMultiple
      hRelative hkTop hRatio (M * C) (mul_pos hM hC)
  exact original_index_bound_of_counter_bound
    k
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    C M hM hkBound hCounter

end

end Euclidean
end Bridge
end PrimeTensor
