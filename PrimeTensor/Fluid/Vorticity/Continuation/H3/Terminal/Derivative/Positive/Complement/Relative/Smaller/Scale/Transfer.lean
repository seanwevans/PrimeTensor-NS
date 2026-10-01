import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Extraction.Example

/-!
# Relative escape with a lower scale for the smaller selected log

The earlier controlled-extraction transfer bounds the original indices
from above by the extracted counter. A different sufficient condition is
available directly on the selected logs: when the smaller log is at least
a positive multiple of the original index, an escaping dominant-to-smaller
ratio forces the dominant log above every original-index multiple. The
relative-gap data alone do not supply this smaller-log lower bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The ratio threshold grows against the extracted counter, while a
linear lower bound for its denominator converts it to a lower bound
against the original selected index. -/
private theorem ratio_escape_with_smaller_linear_scale
    (W L : ℕ → ℝ)
    (k : ℕ → ℕ)
    (hRatio : ∀ n : ℕ, (n : ℝ) + 1 < W n / L n)
    (c : ℝ)
    (hc : 0 < c)
    (hSmaller :
      ∀ᶠ n : ℕ in atTop,
        c * ((k n : ℝ) + 1) ≤ L n)
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) < W n := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (M / c)
  filter_upwards [hSmaller, eventually_ge_atTop N] with n hSmall hn
  have hnCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hIndex : M / c < (n : ℝ) + 1 := by linarith
  have hRatioLower : M / c < W n / L n := hIndex.trans (hRatio n)
  have hKPos : 0 < (k n : ℝ) + 1 := by positivity
  have hLPos : 0 < L n := (mul_pos hc hKPos).trans_le hSmall
  have hWLower : (M / c) * L n < W n :=
    (lt_div_iff₀ hLPos).1 hRatioLower
  calc
    M * (k n : ℝ) ≤ M * ((k n : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith) hM.le
    _ = (M / c) * (c * ((k n : ℝ) + 1)) := by
      field_simp [ne_of_gt hc] <;> ring
    _ ≤ (M / c) * L n :=
      mul_le_mul_of_nonneg_left hSmall (div_nonneg hM.le hc.le)
    _ < W n := hWLower

/-- A linearly large signed curl log lets gradient-dominant relative
escape grow against the original selected index, irrespective of the
rate at which the extraction indices grow. -/
theorem positiveGrowth_gradientRatioEscape_smallerScale_originalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (c : ℝ)
    (hc : 0 < c)
    (hSmaller :
      ∀ᶠ n : ℕ in atTop,
        c * ((k n : ℝ) + 1) ≤
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact ratio_escape_with_smaller_linear_scale
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    k hRatio c hc hSmaller M hM

/-- A linearly large gradient log gives the corresponding original-index
growth in the curl-dominant relative-escape branch. -/
theorem positiveGrowth_curlRatioEscape_smallerScale_originalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (c : ℝ)
    (hc : 0 < c)
    (hSmaller :
      ∀ᶠ n : ℕ in atTop,
        c * ((k n : ℝ) + 1) ≤
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact ratio_escape_with_smaller_linear_scale
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    k hRatio c hc hSmaller M hM

end

end Euclidean
end Bridge
end PrimeTensor
