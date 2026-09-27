import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeEscapeScaleCollapse

/-!
# Exhaustive original-index scale alternative on relative escape

The dominant log normalized by the original selected index is either
eventually bounded or unbounded along a further cofinal extraction. In
the bounded branch, relative ratio escape makes the smaller log
sublinear in that original index. In the cofinal branch, the dominant
normalized log diverges on the further extraction. Neither branch is
selected by this classification.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The two possible original-index rates of a dominant and smaller log
on a previously selected cofinal extraction. -/
def H3TerminalPositiveGrowthOriginalScaleAlternative
    (W L : ℕ → ℝ)
    (k : ℕ → ℕ) : Prop :=
  (∃ C : ℝ,
    (∀ᶠ n : ℕ in atTop,
      W n ≤ C * ((k n : ℝ) + 1))
      ∧
    Tendsto (fun n : ℕ => L n / ((k n : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)))
    ∨
  (∃ j : ℕ → ℕ,
    (∀ n : ℕ,
      n ≤ j n
        ∧
      (n : ℝ) < W (j n) / ((k (j n) : ℝ) + 1))
      ∧
    Tendsto j atTop atTop
      ∧
    Tendsto (fun n : ℕ => k (j n)) atTop atTop
      ∧
    Tendsto
      (fun n : ℕ => W (j n) / ((k (j n) : ℝ) + 1))
      atTop atTop)

/-- Eventual boundedness or cofinal divergence of the dominant log
normalized by the original index, prior to using any relative-ratio
information. -/
private theorem original_scale_bounded_or_cofinal
    (W : ℕ → ℝ)
    (k : ℕ → ℕ)
    (hkTop : Tendsto k atTop atTop) :
    (∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop,
        W n ≤ C * ((k n : ℝ) + 1))
      ∨
    (∃ j : ℕ → ℕ,
      (∀ n : ℕ,
        n ≤ j n
          ∧
        (n : ℝ) < W (j n) / ((k (j n) : ℝ) + 1))
        ∧
      Tendsto j atTop atTop
        ∧
      Tendsto (fun n : ℕ => k (j n)) atTop atTop
        ∧
      Tendsto
        (fun n : ℕ => W (j n) / ((k (j n) : ℝ) + 1))
        atTop atTop) := by
  let R : ℕ → ℝ := fun n => W n / ((k n : ℝ) + 1)
  have hIdentity :
      ∀ᶠ n : ℕ in atTop, (1 + R n) = 1 + R n :=
    Filter.Eventually.of_forall (fun _ => rfl)
  rcases relativeTailAlternative_of_eventually_ratio_identity
      R (fun n => 1 + R n) hIdentity with
    ⟨C, hBound⟩ | ⟨j, hj, hjTop, hRTop, _⟩
  · refine Or.inl ⟨C, ?_⟩
    filter_upwards [hBound] with n hn
    have hIndexPos : 0 < (k n : ℝ) + 1 := by positivity
    exact (div_le_iff₀ hIndexPos).1 hn.1
  · exact Or.inr ⟨j,
      (fun n => ⟨(hj n).1, (hj n).2.1⟩),
      hjTop, hkTop.comp hjTop, hRTop⟩

/-- Gradient-dominant relative escape has either a bounded dominant
original-index rate and a vanishing smaller rate, or a cofinal
original-index superlinear subbranch. -/
theorem positiveGrowth_gradientRatioEscape_originalScaleAlternative
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
    H3TerminalPositiveGrowthOriginalScaleAlternative
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n))) k := by
  unfold H3TerminalPositiveGrowthOriginalScaleAlternative
  rcases original_scale_bounded_or_cofinal
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n))) k hkTop with
    ⟨C, hBound⟩ | hCofinal
  · exact Or.inl ⟨C, hBound,
      positiveGrowth_gradientRatioEscape_boundedDominant_smallerSublinear
        hRelative hkTop hRatio C hBound⟩
  · exact Or.inr hCofinal

/-- The corresponding original-index classification for curl-dominant
relative escape. -/
theorem positiveGrowth_curlRatioEscape_originalScaleAlternative
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
    H3TerminalPositiveGrowthOriginalScaleAlternative
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n))) k := by
  unfold H3TerminalPositiveGrowthOriginalScaleAlternative
  rcases original_scale_bounded_or_cofinal
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n))) k hkTop with
    ⟨C, hBound⟩ | hCofinal
  · exact Or.inl ⟨C, hBound,
      positiveGrowth_curlRatioEscape_boundedDominant_smallerSublinear
        hRelative hkTop hRatio C hBound⟩
  · exact Or.inr hCofinal

end

end Euclidean
end Bridge
end PrimeTensor
