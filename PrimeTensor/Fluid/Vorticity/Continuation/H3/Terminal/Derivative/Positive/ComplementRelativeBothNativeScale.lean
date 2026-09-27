import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeCurlNativeScale
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.ComplementaryGradientCancellationRatio

/-!
# Both selected logs inherit the native index bounds in cancellation

In the cancellation regime the signed selected curl log, viewed in the
selected-gradient orientation, equals the native curl log in its fixed
orientation. The quantitative positive-growth data therefore bound both
selected logs below by the original index. Relative ratio escape in either
dominance direction then outgrows every multiple of that original index.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The cancellation sign identity transfers the indexed native curl
bound to the signed selected curl log at every selected point. -/
theorem positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient) :
    ∀ n : ℕ,
      (n : ℝ) <
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n)
        ∧
      (n : ℝ) <
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n) := by
  intro n
  have hGradient := (hData.1 n).2.2.2.2
  change (n : ℝ) <
    h3TerminalOrientedSelectedGradientLogForPair
      u p sGradient (τ n) (y n) at hGradient
  have hCurl := (hData.1 n).2.2.2.1
  rw [← oriented_selectedSignedNativeCurlLog_eq_oriented_nativeCurlLog_of_cancellation
    u p sCurl sGradient hCancellation (τ n) (y n)] at hCurl
  change (n : ℝ) <
    h3TerminalOrientedSelectedSignedCurlLogForPair
      u p sGradient (τ n) (y n) at hCurl
  exact ⟨hGradient, hCurl⟩

/-- The signed selected curl log supplies the same eventual original-index
lower scale as the selected gradient log. -/
theorem positiveGrowth_signedCurl_halfOriginalIndex_of_cancellation
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
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) * ((k n : ℝ) + 1) ≤
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hkAtLeastOne : ∀ᶠ n : ℕ in atTop, 1 ≤ k n :=
    hkTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hkAtLeastOne] with n hn
  have hnCast : (1 : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hn
  have hCurl :=
    (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
      hData hCancellation (k n)).2
  linarith

/-- In gradient-dominant relative escape, the selected gradient log
outgrows every positive multiple of the original index, without a
linear upper bound on the extraction map. -/
theorem positiveGrowth_gradientRatioEscape_nativeScale_originalIndex
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
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  exact positiveGrowth_gradientRatioEscape_smallerScale_originalIndex
    hRatio (1 / 2) (by norm_num)
    (positiveGrowth_signedCurl_halfOriginalIndex_of_cancellation
      hData hCancellation hkTop) M hM

/-- The bounded dominant branch is excluded also for gradient-dominant
relative escape when the native cancellation identity is retained. -/
theorem positiveGrowth_gradientRatioEscape_nativeScale_not_boundedDominant
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
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
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
    ¬ ∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) ≤
          C * ((k n : ℝ) + 1) := by
  rintro ⟨C, hBound⟩
  have hCollapse :=
    positiveGrowth_gradientRatioEscape_boundedDominant_smallerSublinear
      hRelative hkTop hRatio C hBound
  have hLower :=
    positiveGrowth_signedCurl_halfOriginalIndex_of_cancellation
      hData hCancellation hkTop
  have hUpper :
      ∀ᶠ n : ℕ in atTop,
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1) < (1 / 2 : ℝ) :=
    hCollapse.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n, hnLower, hnUpper⟩ := (hLower.and hUpper).exists
  have hIndexPos : 0 < (k n : ℝ) + 1 := by positivity
  have hnRatioLower :
      (1 / 2 : ℝ) ≤
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          ((k n : ℝ) + 1) :=
    (le_div_iff₀ hIndexPos).2 hnLower
  exact (not_lt_of_ge hnRatioLower) hnUpper

end

end Euclidean
end Bridge
end PrimeTensor
