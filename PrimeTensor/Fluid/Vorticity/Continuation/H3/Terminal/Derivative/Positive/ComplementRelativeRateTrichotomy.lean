import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeClusterCascade

/-!
# Three relative-rate outcomes in the positive-growth triple cascade

The finite normalized-gap cluster `c ≥ 0` separates into ratio matching
when `c = 0` and a persistent positive relative gap when `c > 0`. In the
finite cases the reciprocal ratio tends to `(1 + c)⁻¹`; in the matching case
this is `1`. The remaining cofinal branch has divergent dominant ratio and
vanishing reciprocal. Every selected subsequence retains the complete
quantitative positive-growth native cascade.

These alternatives classify subsequence behavior under the hypothetical
triple native escape; they do not assert which case occurs.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Matching, positive finite separation, or cofinal relative escape,
with the complete quantitative native cascade in each case. -/
def H3TerminalPositiveGrowthRelativeRateTrichotomyLift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (gap ratio reciprocal : ℕ → ℝ) : Prop :=
  (∃ k : ℕ → ℕ,
    StrictMono k
      ∧
    H3TerminalPositiveGrowthQuantitativeNativeData
      u a T p sCurl sGradient
        (fun n => τ (k n)) (fun n => y (k n))
      ∧
    Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 (0 : ℝ))
      ∧
    Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 : ℝ))
      ∧
    Tendsto (fun n : ℕ => reciprocal (k n)) atTop (𝓝 (1 : ℝ)))
    ∨
  (∃ c : ℝ,
    0 < c
      ∧
    ∃ k : ℕ → ℕ,
      StrictMono k
        ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n))
        ∧
      Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c)
        ∧
      Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c))
        ∧
      Tendsto (fun n : ℕ => reciprocal (k n))
        atTop (𝓝 ((1 + c)⁻¹)))
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

/-- Split the finite relative cluster at zero and compute the reciprocal
limit in both finite branches. -/
theorem positiveGrowth_relativeRateTrichotomyLift_of_clusterLift
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {gap ratio reciprocal : ℕ → ℝ}
    (hCluster :
      H3TerminalPositiveGrowthRelativeClusterLift
        u a T p sCurl sGradient τ y gap ratio reciprocal)
    (hReciprocal : ∀ n : ℕ, reciprocal n = (ratio n)⁻¹) :
    H3TerminalPositiveGrowthRelativeRateTrichotomyLift
      u a T p sCurl sGradient τ y gap ratio reciprocal := by
  rcases hCluster with
    ⟨c, hc, k, hkMono, hData', hGapLimit, hRatioLimit⟩ |
    hEscape
  · have hNonzero : (1 + c : ℝ) ≠ 0 := by
      have hPositive : (0 : ℝ) < 1 + c := by linarith
      exact ne_of_gt hPositive
    have hInvLimit :
        Tendsto (fun n : ℕ => (ratio (k n))⁻¹)
          atTop (𝓝 ((1 + c)⁻¹)) :=
      hRatioLimit.inv₀ hNonzero
    have hFunction :
        (fun n : ℕ => reciprocal (k n))
          = (fun n : ℕ => (ratio (k n))⁻¹) := by
      funext n
      exact hReciprocal (k n)
    have hReciprocalLimit :
        Tendsto (fun n : ℕ => reciprocal (k n))
          atTop (𝓝 ((1 + c)⁻¹)) := by
      rw [hFunction]
      exact hInvLimit
    rcases eq_or_lt_of_le hc with hZero | hPositive
    · subst c
      refine Or.inl ⟨k, hkMono, hData', ?_, ?_, ?_⟩
      · simpa using hGapLimit
      · simpa using hRatioLimit
      · simpa using hReciprocalLimit
    · exact Or.inr (Or.inl
        ⟨c, hPositive, k, hkMono, hData',
          hGapLimit, hRatioLimit, hReciprocalLimit⟩)
  · exact Or.inr (Or.inr hEscape)

/-- The relative-rate trichotomy attached to the same oriented triple
native cascade and its prior exact relative-gap conclusions. -/
def H3TerminalPositiveGrowthRelativeRateTrichotomyAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeClusterAt
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
      H3TerminalPositiveGrowthRelativeRateTrichotomyLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (A n - B n) / B n)
          (fun n : ℕ => A n / B n)
          (fun n : ℕ => B n / A n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeRateTrichotomyLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (B n - A n) / A n)
          (fun n : ℕ => B n / A n)
          (fun n : ℕ => A n / B n)))

/-- In the hypothetical triple native branch, relative growth admits a
matching, positively separated, or cofinally escaping subsequence. -/
theorem positiveGrowth_relativeRateTrichotomy_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeRateTrichotomyAt
            u a T p sCurl sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hCluster⟩ :=
    positiveGrowth_relativeCluster_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hCluster, ?_⟩
  dsimp only
  rcases hCluster.2 with ⟨hSame, hLift⟩ | ⟨hOpp, hLift⟩
  · refine Or.inl ⟨hSame, ?_⟩
    apply positiveGrowth_relativeRateTrichotomyLift_of_clusterLift hLift
    intro n
    simp only [inv_div]
  · refine Or.inr ⟨hOpp, ?_⟩
    apply positiveGrowth_relativeRateTrichotomyLift_of_clusterLift hLift
    intro n
    simp only [inv_div]

end

end Euclidean
end Bridge
end PrimeTensor
