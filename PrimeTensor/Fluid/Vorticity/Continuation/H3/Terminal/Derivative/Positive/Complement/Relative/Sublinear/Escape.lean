import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Finite.Scale

/-!
# Relative escape forced by a smaller-log scale deficit

The additive gap exceeds the original index on the synchronized positive-
growth witness. If the index divided by the smaller oriented log diverges
on a strict increasing subsequence, then the normalized gap and the
dominant-to-smaller ratio diverge there, while the reciprocal ratio tends
to zero. Both complementary orientations are treated. This remains a
conditional classification of a subsequence, not a selected outcome.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An indexed additive gap dominates the diverging index quotient, and
the exact ratio identity determines both ratio limits. -/
private theorem relative_escape_of_index_over_smaller_atTop
    (k : ℕ → ℕ)
    (W L : ℕ → ℝ)
    (hIndex : ∀ n : ℕ, (k n : ℝ) < W n - L n)
    (hLPos : ∀ᶠ n : ℕ in atTop, 0 < L n)
    (hIndexTop :
      Tendsto (fun n : ℕ => (k n : ℝ) / L n) atTop atTop) :
    Tendsto (fun n : ℕ => (W n - L n) / L n) atTop atTop
      ∧
    Tendsto (fun n : ℕ => W n / L n) atTop atTop
      ∧
    Tendsto (fun n : ℕ => L n / W n) atTop (𝓝 (0 : ℝ)) := by
  have hGapTop :
      Tendsto (fun n : ℕ => (W n - L n) / L n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [hLPos, (tendsto_atTop.1 hIndexTop) M]
      with n hn hBound
    exact le_trans hBound
      ((div_le_div_iff_of_pos_right hn).2 (hIndex n).le)
  have hRatioEq :
      ∀ᶠ n : ℕ in atTop,
        W n / L n = 1 + (W n - L n) / L n := by
    filter_upwards [hLPos] with n hn
    field_simp [ne_of_gt hn] <;> ring
  have hRatioTop :
      Tendsto (fun n : ℕ => W n / L n) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [(tendsto_atTop.1 hGapTop) M, hRatioEq]
      with n hn hEq
    rw [hEq]
    linarith
  have hInverseTop :
      Tendsto (fun n : ℕ => (W n / L n)⁻¹)
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hRatioTop
  have hInverseEq :
      (fun n : ℕ => L n / W n) =
        (fun n : ℕ => (W n / L n)⁻¹) := by
    funext n
    simp only [inv_div]
  refine ⟨hGapTop, hRatioTop, ?_⟩
  rw [hInverseEq]
  exact hInverseTop

/-- A diverging index-to-signed-curl quotient forces gradient-dominant
relative escape on that same subsequence. -/
theorem positiveGrowth_gradientIndexOverSignedCurl_forces_relativeEscape
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
    (hIndexTop :
      Tendsto
        (fun n : ℕ =>
          (k n : ℝ) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop atTop) :
    Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop atTop
      ∧
    Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
        atTop atTop
      ∧
    Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)) := by
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.2.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨_, hGap, _⟩ | ⟨hOpp, _, _⟩
  · exact relative_escape_of_index_over_smaller_atTop
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n => hGap (k n)) hBPos hIndexTop
  · exact (hOpp hSame).elim

/-- A diverging index-to-gradient quotient forces curl-dominant relative
escape on that same subsequence. -/
theorem positiveGrowth_curlIndexOverGradient_forces_relativeEscape
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
    (hIndexTop :
      Tendsto
        (fun n : ℕ =>
          (k n : ℝ) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop atTop) :
    Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop atTop
      ∧
    Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)))
        atTop atTop
      ∧
    Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ (k n)) (y (k n)) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)) := by
  have hAPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hDominance with ⟨hSame, _, _⟩ | ⟨_, hGap, _⟩
  · exact (hOpp hSame).elim
  · exact relative_escape_of_index_over_smaller_atTop
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n => hGap (k n)) hAPos hIndexTop

end

end Euclidean
end Bridge
end PrimeTensor
