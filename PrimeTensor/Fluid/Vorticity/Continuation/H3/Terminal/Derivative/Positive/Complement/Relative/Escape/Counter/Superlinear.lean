import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Escape.Dominant.Scale

/-!
# Direct dominant-log growth against the extracted counter

The dominant oriented log divided by `n + 1` tends to infinity on a
relative-escape subsequence. Hence it eventually exceeds every fixed
positive multiple of `n + 1`. This quantifies growth against the
extracted counter only; no bound on the original index `k n` is assumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Divergence of the quotient by the positive extracted counter gives
every fixed linear lower bound on the dominant term. -/
private theorem dominant_eventually_above_counter_multiple
    (W : ℕ → ℝ)
    (hTop :
      Tendsto (fun n : ℕ => W n / ((n : ℝ) + 1)) atTop atTop)
    (M : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      M * ((n : ℝ) + 1) < W n := by
  have hBound :
      ∀ᶠ n : ℕ in atTop,
        M < W n / ((n : ℝ) + 1) :=
    hTop.eventually (eventually_gt_atTop M)
  filter_upwards [hBound] with n hn
  have hCounterPos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact (lt_div_iff₀ hCounterPos).1 hn

/-- Gradient-dominant escape outgrows every fixed multiple of the
extracted counter. -/
theorem positiveGrowth_gradientRatioEscape_forces_everyCounterMultiple
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
              u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (_hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * ((n : ℝ) + 1) <
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact dominant_eventually_above_counter_multiple
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (positiveGrowth_gradientRatioEscape_forces_dominantOverCounter
      hRelative hkTop hRatio) M

/-- Curl-dominant escape outgrows every fixed multiple of the
extracted counter. -/
theorem positiveGrowth_curlRatioEscape_forces_everyCounterMultiple
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
              u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (_hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * ((n : ℝ) + 1) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact dominant_eventually_above_counter_multiple
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (positiveGrowth_curlRatioEscape_forces_dominantOverCounter
      hRelative hkTop hRatio) M

end

end Euclidean
end Bridge
end PrimeTensor
