import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Reindex.Cascade

/-!
# Vanishing reciprocal in the relative escape branch

The cofinal relative-escape branch has a dominant-to-smaller ratio tending
to `+∞`. Its reciprocal therefore tends to zero. The field identity
`(A / B)⁻¹ = B / A` identifies this with the smaller-to-dominant ratio,
including the zero conventions at any initial indices. The bounded relative
branch is retained without asserting convergence there.

The same extracted sequence still carries the complete quantitative
positive-growth native cascade.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Strengthen the lifted relative alternative with the vanishing reciprocal
on its cofinal escape branch. -/
def H3TerminalPositiveGrowthRelativeReciprocalLift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (gap ratio reciprocal : ℕ → ℝ) : Prop :=
  (∃ C : ℝ,
    ∀ᶠ n : ℕ in atTop,
      gap n ≤ C ∧ ratio n ≤ 1 + C)
    ∨
  (∃ k : ℕ → ℕ,
    H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n))
      ∧
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
    Tendsto (fun n : ℕ => ratio (k n)) atTop atTop
      ∧
    Tendsto (fun n : ℕ => reciprocal (k n)) atTop (𝓝 (0 : ℝ)))

/-- A diverging dominant ratio makes its reciprocal vanish on the same
cofinal positive-growth subsequence. -/
theorem positiveGrowth_relativeReciprocalLift_of_tailLift
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {gap ratio reciprocal : ℕ → ℝ}
    (hLift :
      H3TerminalPositiveGrowthRelativeTailLift
        u a T p sCurl sGradient τ y gap ratio)
    (hReciprocal : ∀ n : ℕ, reciprocal n = (ratio n)⁻¹) :
    H3TerminalPositiveGrowthRelativeReciprocalLift
      u a T p sCurl sGradient τ y gap ratio reciprocal := by
  rcases hLift with hBound |
    ⟨k, hData', hk, hkTop, hGapTop, hRatioTop⟩
  · exact Or.inl hBound
  · have hInvTop :
        Tendsto (fun n : ℕ => (ratio (k n))⁻¹)
          atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hRatioTop
    have hFunction :
        (fun n : ℕ => reciprocal (k n))
          = (fun n : ℕ => (ratio (k n))⁻¹) := by
      funext n
      exact hReciprocal (k n)
    have hReciprocalTop :
        Tendsto (fun n : ℕ => reciprocal (k n))
          atTop (𝓝 (0 : ℝ)) := by
      rw [hFunction]
      exact hInvTop
    exact Or.inr
      ⟨k, hData', hk, hkTop, hGapTop, hRatioTop, hReciprocalTop⟩

/-- Both complementary orientations express the vanishing reciprocal as
the correctly ordered smaller-to-dominant oriented logarithm ratio. -/
def H3TerminalPositiveGrowthRelativeReciprocalAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeTailLiftedAt
      u a T p sCurl sGradient sComplement τ y
    ∧
  (let A : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n);
   let B : ℕ → ℝ := fun n =>
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n);
   (sComplement = sGradient
      ∧
      H3TerminalPositiveGrowthRelativeReciprocalLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (A n - B n) / B n)
          (fun n : ℕ => A n / B n)
          (fun n : ℕ => B n / A n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeReciprocalLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (B n - A n) / A n)
          (fun n : ℕ => B n / A n)
          (fun n : ℕ => A n / B n)))

/-- Hypothetical triple native escape has either an eventually bounded
relative gap or a full positive-growth subsequence on which the dominant
ratio diverges and the reciprocal smaller ratio tends to zero. -/
theorem positiveGrowth_relativeReciprocal_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeReciprocalAt
            u a T p sCurl sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hLifted⟩ :=
    positiveGrowth_relativeTailLifted_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hLifted, ?_⟩
  dsimp only
  rcases hLifted.2 with ⟨hSame, hLift⟩ | ⟨hOpp, hLift⟩
  · refine Or.inl ⟨hSame, ?_⟩
    apply positiveGrowth_relativeReciprocalLift_of_tailLift hLift
    intro n
    simp only [inv_div]
  · refine Or.inr ⟨hOpp, ?_⟩
    apply positiveGrowth_relativeReciprocalLift_of_tailLift hLift
    intro n
    simp only [inv_div]

end

end Euclidean
end Bridge
end PrimeTensor
