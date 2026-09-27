import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeSmallerScaleTransfer

/-!
# Smaller-log scale in a bounded dominant relative-escape branch

If the dominant-to-smaller ratio escapes while the dominant log remains
bounded by a fixed multiple of the original selected index, the smaller
log divided by that index must tend to zero. This identifies the scale
left open by the original-index transfer criterion; it does not decide
whether the bounded dominant branch occurs for the positive-growth data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A bounded dominant original-index scale and an escaping ratio force
the positive smaller term to have vanishing original-index scale. -/
private theorem smaller_over_original_zero_of_bounded_dominant_ratio_escape
    (W L : ℕ → ℝ)
    (k : ℕ → ℕ)
    (hLPos : ∀ᶠ n : ℕ in atTop, 0 < L n)
    (hRatio : ∀ n : ℕ, (n : ℝ) + 1 < W n / L n)
    (C : ℝ)
    (hWBound :
      ∀ᶠ n : ℕ in atTop,
        W n ≤ C * ((k n : ℝ) + 1)) :
    Tendsto (fun n : ℕ => L n / ((k n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [hLPos] with n hn
    have hIndexPos : 0 < (k n : ℝ) + 1 := by positivity
    exact ha.trans_le (div_nonneg hn.le hIndexPos.le)
  · intro ε hε
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C / ε)
    filter_upwards [hLPos, hWBound, eventually_ge_atTop N]
      with n hn hBound hnIndex
    have hnCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnIndex
    have hCounterPos : 0 < (n : ℝ) + 1 := by positivity
    have hOrigPos : 0 < (k n : ℝ) + 1 := by positivity
    have hCoef : C < ε * ((n : ℝ) + 1) := by
      have hThreshold : C / ε < (n : ℝ) + 1 := by linarith
      have hMultiplied := (div_lt_iff₀ hε).1 hThreshold
      nlinarith
    have hRatioProduct : ((n : ℝ) + 1) * L n < W n :=
      (lt_div_iff₀ hn).1 (hRatio n)
    have hProduct :
        ((n : ℝ) + 1) * L n <
          ((n : ℝ) + 1) * (ε * ((k n : ℝ) + 1)) := by
      calc
        ((n : ℝ) + 1) * L n < W n := hRatioProduct
        _ ≤ C * ((k n : ℝ) + 1) := hBound
        _ < (ε * ((n : ℝ) + 1)) * ((k n : ℝ) + 1) :=
          mul_lt_mul_of_pos_right hCoef hOrigPos
        _ = ((n : ℝ) + 1) * (ε * ((k n : ℝ) + 1)) := by ring
    have hSmall : L n < ε * ((k n : ℝ) + 1) := by
      by_contra hNot
      have hReverse :
          ((n : ℝ) + 1) * (ε * ((k n : ℝ) + 1)) ≤
            ((n : ℝ) + 1) * L n :=
        mul_le_mul_of_nonneg_left (le_of_not_gt hNot) hCounterPos.le
      exact (not_lt_of_ge hReverse) hProduct
    exact (div_lt_iff₀ hOrigPos).2 hSmall

/-- If the gradient log has bounded original-index growth during
gradient-dominant escape, the signed curl log becomes sublinear there. -/
theorem positiveGrowth_gradientRatioEscape_boundedDominant_smallerSublinear
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
    (C : ℝ)
    (hWBound :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) ≤
          C * ((k n : ℝ) + 1)) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
  have hLPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.2.1.comp hkTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  exact smaller_over_original_zero_of_bounded_dominant_ratio_escape
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    k hLPos hRatio C hWBound

/-- If the signed curl log has bounded original-index growth during
curl-dominant escape, the selected gradient log becomes sublinear there. -/
theorem positiveGrowth_curlRatioEscape_boundedDominant_smallerSublinear
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
    (C : ℝ)
    (hWBound :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) ≤
          C * ((k n : ℝ) + 1)) :
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
  have hLPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.1.comp hkTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  exact smaller_over_original_zero_of_bounded_dominant_ratio_escape
    (fun n : ℕ =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    (fun n : ℕ =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ (k n)) (y (k n)))
    k hLPos hRatio C hWBound

end

end Euclidean
end Bridge
end PrimeTensor
