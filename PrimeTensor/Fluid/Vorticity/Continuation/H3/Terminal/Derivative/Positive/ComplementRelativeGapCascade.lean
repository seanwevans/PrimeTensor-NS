import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementDominanceCascade

/-!
# Relative gap identity in the positive-growth triple native branch

The cancellation-compatible triple branch gives two positive oriented terms,
the selected gradient `Aₙ` and correctly signed curl `Bₙ`, both tending to
`+∞`.  Additive dominance says that one difference exceeds `n`.

Once the smaller term is positive, the dominant-to-smaller ratio is exactly
`1 + (additive gap)/(smaller term)`.  The relative gap is positive, but its
limit is not determined by the additive gap alone.  This identity isolates the
additional rate estimate needed to decide asymptotic ratio matching in the
unbounded complementary branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The oriented gradient and signed curl both diverge, and the ratio of the
larger to the smaller has a positive exact normalized-gap correction on a
terminal tail. -/
def H3TerminalPositiveGrowthRelativeGapAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n))
      atTop atTop
    ∧
  ((sComplement = sGradient
      ∧
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)
          ∧
        0 <
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)
          ∧
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n)
          =
        1 +
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n))
    ∨
    (sComplement ≠ sGradient
      ∧
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)
          ∧
        0 <
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)
          ∧
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n)
          =
        1 +
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)))

/-- The triple native cascade has an exact positive relative-gap identity
on the same sequence that retains the full positive-growth data. -/
theorem positiveGrowth_relativeGap_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeGapAt
            u p sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hDominance⟩ :=
    positiveGrowth_complementDominance_of_tripleNativeCascade
      hTriple

  have hGradientEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeGradientForPair u p (τ n) (y n))
        sGradient := by
    rcases hData with ⟨_, _, _, _, _, _, _, hGradientEscape, _⟩
    exact hGradientEscape

  have hCurlEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeCurlForPair u p (τ n) (y n))
        sCurl := by
    rcases hData with ⟨_, _, _, _, _, _, hCurlEscape, _, _⟩
    exact hCurlEscape

  have hATop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop := by
    exact orientedLog_tendsto_atTop_of_nativeDirectionalEscape
      hGradientEscape

  have hBTop :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
        atTop atTop := by
    exact oriented_selectedSignedNativeCurlLog_tendsto_atTop_of_cancellation
      hCancellation hCurlEscape

  refine ⟨τ, y, hData, hCancellation, ?_⟩
  unfold H3TerminalPositiveGrowthRelativeGapAt
  refine ⟨hATop, hBTop, ?_⟩
  rcases hDominance with hGradientDominates | hCurlDominates
  · obtain ⟨hSame, hGap, _⟩ := hGradientDominates
    refine Or.inl ⟨hSame, ?_⟩
    have hBPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n) :=
      hBTop.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hBPos] with n hn
    have hGapPos :
        0 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n) := by
      have hIndex : (0 : ℝ) ≤ n := by positivity
      exact lt_of_le_of_lt hIndex (hGap n)
    refine ⟨hn, div_pos hGapPos hn, ?_⟩
    have hn0 :
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n) ≠ 0 := ne_of_gt hn
    field_simp [hn0] <;> ring
  · obtain ⟨hOpp, hGap, _⟩ := hCurlDominates
    refine Or.inr ⟨hOpp, ?_⟩
    have hAPos :
        ∀ᶠ n : ℕ in atTop,
          0 < h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n) :=
      hATop.eventually (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hAPos] with n hn
    have hGapPos :
        0 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ n) (y n)
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ n) (y n) := by
      have hIndex : (0 : ℝ) ≤ n := by positivity
      exact lt_of_le_of_lt hIndex (hGap n)
    refine ⟨hn, div_pos hGapPos hn, ?_⟩
    have hn0 :
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n) ≠ 0 := ne_of_gt hn
    field_simp [hn0] <;> ring

end

end Euclidean
end Bridge
end PrimeTensor
