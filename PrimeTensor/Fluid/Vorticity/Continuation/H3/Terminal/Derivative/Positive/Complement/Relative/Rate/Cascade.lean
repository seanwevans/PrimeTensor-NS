import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Gap.Cascade

/-!
# Finite relative rates in the positive-growth triple cascade

The two oriented logarithms in the triple-escape branch both tend to `+∞`,
while their additive difference also tends to `+∞`.  The exact relative-gap
identity gives a separate finite-rate test: the dominant-to-smaller ratio
tends to `1 + c` if and only if the additive difference divided by the
smaller term tends to `c`.  In particular, asymptotic ratio matching is
equivalent to a vanishing normalized gap; additive divergence alone does
not decide it.

The test holds on the same sequence that carries all the quantitative
positive-growth data, with the dominant term selected by the complementary
orientation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A positive eventual denominator makes every finite ratio limit equivalent
to the corresponding normalized additive-gap limit. -/
private theorem ratio_limit_iff_normalized_gap_limit
    (A B : ℕ → ℝ)
    (hBPos : ∀ᶠ n : ℕ in atTop, 0 < B n)
    (c : ℝ) :
    Tendsto (fun n : ℕ => A n / B n) atTop (𝓝 (1 + c))
      ↔
    Tendsto (fun n : ℕ => (A n - B n) / B n) atTop (𝓝 c) := by
  have hEq :
      (fun n : ℕ => A n / B n - 1) =ᶠ[atTop]
        (fun n : ℕ => (A n - B n) / B n) := by
    filter_upwards [hBPos] with n hn
    field_simp [ne_of_gt hn] <;> ring
  constructor
  · intro hRatio
    have hSub :
        Tendsto (fun n : ℕ => A n / B n - 1) atTop
          (𝓝 ((1 + c) - 1)) :=
      hRatio.sub_const 1
    have hSub' :
        Tendsto (fun n : ℕ => A n / B n - 1) atTop (𝓝 c) := by
      have hArithmetic : (1 + c) - 1 = c := by ring
      simpa only [hArithmetic] using hSub
    exact hSub'.congr' hEq
  · intro hGap
    have hSub :
        Tendsto (fun n : ℕ => A n / B n - 1) atTop (𝓝 c) :=
      hGap.congr' hEq.symm
    have hAdd :
        Tendsto (fun n : ℕ => 1 + (A n / B n - 1)) atTop
          (𝓝 (1 + c)) :=
      hSub.const_add 1
    have hRewrite :
        (fun n : ℕ => 1 + (A n / B n - 1))
          = (fun n : ℕ => A n / B n) := by
      funext n
      ring
    rw [hRewrite] at hAdd
    exact hAdd

/-- The previous exact relative gap, together with the finite-rate criterion
for the winner and loser selected by the complementary orientation. -/
def H3TerminalPositiveGrowthRelativeRateAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeGapAt
      u p sGradient sComplement τ y
    ∧
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient
      ∧
      ∀ c : ℝ,
        Tendsto (fun n : ℕ => A n / B n) atTop (𝓝 (1 + c))
          ↔
        Tendsto (fun n : ℕ => (A n - B n) / B n) atTop (𝓝 c))
    ∨
    (sComplement ≠ sGradient
      ∧
      ∀ c : ℝ,
        Tendsto (fun n : ℕ => B n / A n) atTop (𝓝 (1 + c))
          ↔
        Tendsto (fun n : ℕ => (B n - A n) / A n) atTop (𝓝 c)))

/-- In the triple native branch, all finite relative-rate tests hold on the
original positive-growth sequence supplied by the relative-gap cascade. -/
theorem positiveGrowth_relativeRate_of_tripleNativeCascade
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u a T p sCurl sGradient sComplement) :
    ∃ τ : ℕ → ℝ,
      ∃ y : ℕ → Point3,
        H3TerminalPositiveGrowthQuantitativeNativeData
            u a T p sCurl sGradient τ y
          ∧
        H3TerminalComplementCancellationRegime
            p sCurl sGradient
          ∧
        H3TerminalPositiveGrowthRelativeRateAt
            u p sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hRelativeGap⟩ :=
    positiveGrowth_relativeGap_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hRelativeGap, ?_⟩
  dsimp only
  obtain ⟨_hATop, _hBTop, hBranch⟩ := hRelativeGap
  rcases hBranch with ⟨hSame, hTail⟩ | ⟨hOpp, hTail⟩
  · refine Or.inl ⟨hSame, ?_⟩
    have hBPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n) := by
      filter_upwards [hTail] with n hn
      exact hn.1
    intro c
    exact ratio_limit_iff_normalized_gap_limit
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n))
      hBPos c
  · refine Or.inr ⟨hOpp, ?_⟩
    have hAPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n) := by
      filter_upwards [hTail] with n hn
      exact hn.1
    intro c
    exact ratio_limit_iff_normalized_gap_limit
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n))
      hAPos c

end

end Euclidean
end Bridge
end PrimeTensor
