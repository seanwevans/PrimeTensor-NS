import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Rate.Cascade

/-!
# Relative-gap tail alternatives in the positive-growth triple cascade

Finite relative-rate tests leave open the possibility that the normalized
gap has no finite limit. Every normalized-gap sequence is either eventually
bounded above or admits a cofinal index map on which it exceeds the index.
The exact ratio identity transfers these two quantitative alternatives to
the dominant-to-smaller ratio. An oscillating unbounded ratio belongs to the
second branch after extraction; it need not diverge on the original sequence.

The original time and point sequence retains its full positive-growth data.
The extracted indices tend to `+∞`, so existing limits also hold when
composed with that index map.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Either the normalized gap and ratio have an eventual common ceiling, or
a cofinal subsequence makes both exceed a growing index threshold. -/
def H3TerminalRelativeTailAlternative
    (gap ratio : ℕ → ℝ) : Prop :=
  (∃ C : ℝ,
    ∀ᶠ n : ℕ in atTop,
      gap n ≤ C ∧ ratio n ≤ 1 + C)
    ∨
  (∃ k : ℕ → ℕ,
    (∀ n : ℕ,
      n ≤ k n
        ∧
      (n : ℝ) < gap (k n)
        ∧
      (n : ℝ) + 1 < ratio (k n))
      ∧
    Tendsto k atTop atTop
      ∧
    Tendsto (fun n : ℕ => gap (k n)) atTop atTop
      ∧
    Tendsto (fun n : ℕ => ratio (k n)) atTop atTop)

private theorem tendsto_real_atTop_of_index_lt_rate
    {f : ℕ → ℝ}
    (hf : ∀ n : ℕ, (n : ℝ) < f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact le_of_lt (lt_trans (lt_of_lt_of_le hN hCast) (hf n))

/-- The tail alternative follows solely from the eventual exact ratio
identity. The unbounded branch is cofinal even when the full sequence
oscillates. -/
theorem relativeTailAlternative_of_eventually_ratio_identity
    (gap ratio : ℕ → ℝ)
    (hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n) :
    H3TerminalRelativeTailAlternative gap ratio := by
  classical
  unfold H3TerminalRelativeTailAlternative
  by_cases hBound : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, gap n ≤ C
  · obtain ⟨C, hC⟩ := hBound
    refine Or.inl ⟨C, ?_⟩
    filter_upwards [hC, hEq] with n hn hRatio
    exact ⟨hn, by rw [hRatio]; linarith⟩
  · have hCofinal :
        ∀ N : ℕ, ∀ M : ℝ,
          ∃ m : ℕ, N ≤ m ∧ M < gap m := by
      intro N M
      by_contra hNone
      apply hBound
      refine ⟨M, ?_⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      exact le_of_not_gt (fun hGreater =>
        hNone ⟨n, hn, hGreater⟩)
    obtain ⟨N, hEqTail⟩ := eventually_atTop.1 hEq
    have hChoice :
        ∀ n : ℕ,
          ∃ m : ℕ,
            n ≤ m
              ∧
            (n : ℝ) < gap m
              ∧
            (n : ℝ) + 1 < ratio m := by
      intro n
      obtain ⟨m, hm, hGap⟩ := hCofinal (max n N) (n : ℝ)
      have hnle : n ≤ m := le_trans (le_max_left n N) hm
      have hNle : N ≤ m := le_trans (le_max_right n N) hm
      have hRatio : (n : ℝ) + 1 < ratio m := by
        rw [hEqTail m hNle]
        linarith
      exact ⟨m, hnle, hGap, hRatio⟩
    choose k hk using hChoice
    have hkTop : Tendsto k atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro N'
      filter_upwards [eventually_ge_atTop N'] with n hn
      exact le_trans hn (hk n).1
    have hGapTop :
        Tendsto (fun n : ℕ => gap (k n)) atTop atTop :=
      tendsto_real_atTop_of_index_lt_rate
        (fun n => (hk n).2.1)
    have hRatioTop :
        Tendsto (fun n : ℕ => ratio (k n)) atTop atTop := by
      apply tendsto_real_atTop_of_index_lt_rate
      intro n
      have hIndex : (n : ℝ) < (n : ℝ) + 1 := by linarith
      exact lt_trans hIndex (hk n).2.2
    exact Or.inr ⟨k, hk, hkTop, hGapTop, hRatioTop⟩

/-- The relative-rate criterion and the exhaustive tail alternative, with
the dominant term determined by the complementary orientation. -/
def H3TerminalPositiveGrowthRelativeTailAlternativeAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeRateAt
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
      H3TerminalRelativeTailAlternative
        (fun n : ℕ => (A n - B n) / B n)
        (fun n : ℕ => A n / B n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalRelativeTailAlternative
        (fun n : ℕ => (B n - A n) / A n)
        (fun n : ℕ => B n / A n)))

/-- The triple-escape branch has an eventually bounded relative gap or a
cofinal subsequence where the relative gap and ratio both diverge. The full
positive-growth witness and the earlier finite-rate criterion are retained. -/
theorem positiveGrowth_relativeTailAlternative_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeTailAlternativeAt
            u p sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hRate⟩ :=
    positiveGrowth_relativeRate_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hRate, ?_⟩
  dsimp only
  obtain ⟨_hATop, _hBTop, hBranches⟩ := hRate.1
  rcases hBranches with ⟨hSame, hTail⟩ | ⟨hOpp, hTail⟩
  · refine Or.inl ⟨hSame, ?_⟩
    apply relativeTailAlternative_of_eventually_ratio_identity
    filter_upwards [hTail] with n hn
    exact hn.2.2
  · refine Or.inr ⟨hOpp, ?_⟩
    apply relativeTailAlternative_of_eventually_ratio_identity
    filter_upwards [hTail] with n hn
    exact hn.2.2

end

end Euclidean
end Bridge
end PrimeTensor
