import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Finite.Both.Logs

/-!
# Dominant-log scale on a relative-escape subsequence

In the cofinal relative-escape branch, the dominant-to-smaller ratio is
greater than `n + 1` at extracted counter `n`. The smaller oriented log
still tends to infinity. Consequently the dominant log divided by `n + 1`
tends to infinity on that subsequence. The counter `n` is distinct from
the original selected index `k n`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An unbounded smaller quantity and a dominant ratio above the extracted
counter force the dominant quantity to outgrow that counter. -/
private theorem dominant_over_counter_atTop_of_ratio_escape
    (W L : ℕ → ℝ)
    (hLTop : Tendsto L atTop atTop)
    (hRatio : ∀ n : ℕ, (n : ℝ) + 1 < W n / L n) :
    Tendsto (fun n : ℕ => W n / ((n : ℝ) + 1)) atTop atTop := by
  have hLPos : ∀ᶠ n : ℕ in atTop, 0 < L n :=
    hLTop.eventually (eventually_gt_atTop (0 : ℝ))
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [hLPos, (tendsto_atTop.1 hLTop) M]
    with n hn hLower
  have hCounterPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hDominant : ((n : ℝ) + 1) * L n < W n :=
    (lt_div_iff₀ hn).1 (hRatio n)
  have hNormalized :
      L n < W n / ((n : ℝ) + 1) := by
    apply (lt_div_iff₀ hCounterPos).2
    simpa [mul_comm] using hDominant
  exact hLower.trans hNormalized.le

/-- Gradient-dominant ratio escape forces the selected gradient logarithm
to outgrow the extracted counter `n + 1`. -/
theorem positiveGrowth_gradientRatioEscape_forces_dominantOverCounter
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
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
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((n : ℝ) + 1))
      atTop atTop := by
  exact dominant_over_counter_atTop_of_ratio_escape
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (hRelative.2.1.comp hkTop) hRatio

/-- Curl-dominant ratio escape forces the signed curl logarithm to
outgrow the extracted counter `n + 1`. -/
theorem positiveGrowth_curlRatioEscape_forces_dominantOverCounter
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
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
              u p sGradient (τ (k n)) (y (k n))) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((n : ℝ) + 1))
      atTop atTop := by
  exact dominant_over_counter_atTop_of_ratio_escape
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (hRelative.1.comp hkTop) hRatio

end

end Euclidean
end Bridge
end PrimeTensor
