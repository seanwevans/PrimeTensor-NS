import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Matching.Cascade

/-!
# Smaller-log scale at a finite relative-gap cluster

An indexed additive gap is strictly larger than the original subsequence
index. At a finite normalized-gap cluster `c`, division by the positive
smaller log bounds the index-to-log quotient by `c + ε` eventually, for
every `ε > 0`. The result applies to either orientation on the synchronized
positive-growth witness. It does not assert that a finite cluster occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An indexed gap and a finite normalized-gap limit give the precise
eventual upper bound on index divided by the smaller denominator. -/
private theorem index_div_eventually_lt_of_gap_limit
    (k : ℕ → ℕ)
    (G D : ℕ → ℝ)
    (c ε : ℝ)
    (hIndex : ∀ n : ℕ, (k n : ℝ) < G n)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hGapLimit :
      Tendsto (fun n : ℕ => G n / D n) atTop (𝓝 c))
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) / D n < c + ε := by
  have hGapUpper :
      ∀ᶠ n : ℕ in atTop, G n / D n < c + ε :=
    hGapLimit.eventually (Iio_mem_nhds (lt_add_of_pos_right c hε))
  filter_upwards [hDPos, hGapUpper] with n hn hUpper
  exact ((div_lt_div_iff_of_pos_right hn).2 (hIndex n)).trans hUpper

/-- A finite normalized gap in the gradient-dominant orientation bounds
the original index relative to the signed curl logarithm. -/
theorem positiveGrowth_gradientFiniteGap_bounds_indexOverSignedCurl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hDominance :
      H3TerminalPositiveGrowthComplementDominanceAt
        u p sGradient sComplement τ y)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
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
      (k n : ℝ) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) < c + ε := by
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.2.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨_, hGap, _⟩ | ⟨hOpp, _, _⟩
  · exact index_div_eventually_lt_of_gap_limit
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n))
          - h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      c ε (fun n => hGap (k n)) hBPos hFinite hε
  · exact (hOpp hSame).elim

/-- A finite normalized gap in the curl-dominant orientation bounds the
original index relative to the selected gradient logarithm. -/
theorem positiveGrowth_curlFiniteGap_bounds_indexOverGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {p : H3TerminalCurlGradientPair}
    {sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hDominance :
      H3TerminalPositiveGrowthComplementDominanceAt
        u p sGradient sComplement τ y)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
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
      (k n : ℝ) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) < c + ε := by
  have hAPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨hSame, _, _⟩ | ⟨_, hGap, _⟩
  · exact (hOpp hSame).elim
  · exact index_div_eventually_lt_of_gap_limit
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n))
          - h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      c ε (fun n => hGap (k n)) hAPos hFinite hε

end

end Euclidean
end Bridge
end PrimeTensor
