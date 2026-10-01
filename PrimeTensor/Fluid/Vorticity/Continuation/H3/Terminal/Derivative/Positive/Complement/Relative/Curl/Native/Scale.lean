import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Original.Scale.Alternative

/-!
# Native gradient scale in curl-dominant relative escape

The selected oriented gradient log is the quantitative native gradient
log itself. It exceeds the original witness index at every point. Thus
in the curl-dominant relative-escape branch the smaller log has a linear
original-index lower bound. The previously conditional smaller-scale
transfer now applies without a bound on the extraction map.

This argument concerns the curl-dominant branch. In the gradient-dominant
branch the smaller term is the signed selected curl log, for which the
quantitative native data do not give the same index bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The quantitative native gradient bound supplies half the original
index plus one as an eventual lower scale along every cofinal extraction. -/
theorem positiveGrowth_nativeGradient_halfOriginalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * ((k n : ℝ) + 1) ≤
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hkAtLeastOne : ∀ᶠ n : ℕ in atTop, 1 ≤ k n :=
    hkTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hkAtLeastOne] with n hn
  have hnCast : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hn
  have hGradient := (hData.1 (k n)).2.2.2.2
  change (k n : ℝ) <
    h3TerminalOrientedSelectedGradientLogForPair
      u p sGradient (τ (k n)) (y (k n)) at hGradient
  linarith

/-- Curl-dominant relative escape forces the signed selected curl log
above every positive multiple of the original index `k n`. -/
theorem positiveGrowth_curlRatioEscape_nativeScale_originalIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact positiveGrowth_curlRatioEscape_smallerScale_originalIndex
    hRatio (1 / 2) (by norm_num)
    (positiveGrowth_nativeGradient_halfOriginalIndex hData hkTop) M hM

/-- The bounded dominant option in the original-scale alternative is
incompatible with the quantitative native gradient bound in curl-dominant
relative escape. -/
theorem positiveGrowth_curlRatioEscape_nativeScale_not_boundedDominant
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
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
    ¬ ∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) ≤
          C * ((k n : ℝ) + 1) := by
  rintro ⟨C, hBound⟩
  have hCollapse :=
    positiveGrowth_curlRatioEscape_boundedDominant_smallerSublinear
      hRelative hkTop hRatio C hBound
  have hLower := positiveGrowth_nativeGradient_halfOriginalIndex
    hData hkTop
  have hUpper :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1) < (1 / 2 : ℝ) :=
    hCollapse.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n, hnLower, hnUpper⟩ := (hLower.and hUpper).exists
  have hIndexPos : 0 < (k n : ℝ) + 1 := by positivity
  have hnRatioLower :
      (1 / 2 : ℝ) ≤
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1) :=
    (le_div_iff₀ hIndexPos).2 hnLower
  exact (not_lt_of_ge hnRatioLower) hnUpper

end

end Euclidean
end Bridge
end PrimeTensor
