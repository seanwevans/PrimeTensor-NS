import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeReciprocalCascade
import Mathlib.Topology.Sequences

/-!
# Finite relative-rate clusters in the bounded positive-growth branch

The normalized additive gap is eventually positive. If it is also bounded
above, compactness of a real interval supplies a cofinal subsequence with
a finite limit `c ≥ 0`. The exact ratio identity gives a dominant-to-smaller
ratio limit of `1 + c` on that same subsequence. The quantitative native
positive-growth cascade survives the extraction.

The other branch retains the earlier cofinal ratio escape and vanishing
reciprocal. Neither branch asserts a limit on the unextracted sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The bounded relative branch has a finite, nonnegative cluster rate;
the escaping branch retains the full cascade and vanishing reciprocal. -/
def H3TerminalPositiveGrowthRelativeClusterLift
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3)
    (gap ratio reciprocal : ℕ → ℝ) : Prop :=
  (∃ c : ℝ,
    0 ≤ c
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
      Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c)))
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

/-- Compactness extracts a finite normalized-gap cluster from the bounded
branch; the exact relative identity transfers the cluster to the ratio. -/
theorem positiveGrowth_relativeClusterLift_of_reciprocalLift
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {gap ratio reciprocal : ℕ → ℝ}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hPos : ∀ᶠ n : ℕ in atTop, 0 ≤ gap n)
    (hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n)
    (hLift :
      H3TerminalPositiveGrowthRelativeReciprocalLift
        u a T p sCurl sGradient τ y gap ratio reciprocal) :
    H3TerminalPositiveGrowthRelativeClusterLift
      u a T p sCurl sGradient τ y gap ratio reciprocal := by
  classical
  rcases hLift with ⟨C, hBound⟩ |
    ⟨k, hData', hk, hkTop, hGapTop, hRatioTop, hReciprocalTop⟩
  · have hInInterval :
        ∀ᶠ n : ℕ in atTop, gap n ∈ Set.Icc (0 : ℝ) C := by
      filter_upwards [hPos, hBound] with n hn hCeiling
      exact ⟨hn, hCeiling.1⟩
    obtain ⟨c, hc, k, hkMono, hGapLimit⟩ :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).tendsto_subseq'
        hInInterval.frequently
    have hkTop : Tendsto k atTop atTop := hkMono.tendsto_atTop
    have hEqK :
        ∀ᶠ n : ℕ in atTop,
          ratio (k n) = 1 + gap (k n) :=
      hkTop.eventually hEq
    have hAddLimit :
        Tendsto (fun n : ℕ => 1 + gap (k n))
          atTop (𝓝 (1 + c)) :=
      hGapLimit.const_add 1
    have hRatioLimit :
        Tendsto (fun n : ℕ => ratio (k n))
          atTop (𝓝 (1 + c)) := by
      have hEqK' :
          ∀ᶠ n : ℕ in atTop,
            1 + gap (k n) = ratio (k n) := by
        filter_upwards [hEqK] with n hn
        exact hn.symm
      exact hAddLimit.congr' hEqK'
    have hData' :
        H3TerminalPositiveGrowthQuantitativeNativeData
          u a T p sCurl sGradient
            (fun n => τ (k n)) (fun n => y (k n)) :=
      positiveGrowth_quantitativeNativeData_comp_cofinal hData
        (fun n => hkMono.le_apply)
    exact Or.inl ⟨c, hc.1, k, hkMono, hData', hGapLimit, hRatioLimit⟩
  · exact Or.inr
      ⟨k, hData', hk, hkTop, hGapTop, hRatioTop, hReciprocalTop⟩

/-- Orientation-aware finite-cluster or reciprocal-escape alternative,
retaining the earlier exact relative-gap and tail statements. -/
def H3TerminalPositiveGrowthRelativeClusterAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalPositiveGrowthRelativeReciprocalAt
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
      H3TerminalPositiveGrowthRelativeClusterLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (A n - B n) / B n)
          (fun n : ℕ => A n / B n)
          (fun n : ℕ => B n / A n))
    ∨
    (sComplement ≠ sGradient
      ∧
      H3TerminalPositiveGrowthRelativeClusterLift
        u a T p sCurl sGradient τ y
          (fun n : ℕ => (B n - A n) / A n)
          (fun n : ℕ => B n / A n)
          (fun n : ℕ => A n / B n)))

/-- The triple native cascade admits either a finite nonnegative relative
cluster rate or a cofinal diverging ratio with vanishing reciprocal, with
complete quantitative positive-growth data on the selected subsequence. -/
theorem positiveGrowth_relativeCluster_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthRelativeClusterAt
            u a T p sCurl sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hReciprocal⟩ :=
    positiveGrowth_relativeReciprocal_of_tripleNativeCascade hTriple
  have hRelativeGap :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y :=
    hReciprocal.1.1.1.1
  obtain ⟨_hATop, _hBTop, hGapBranches⟩ := hRelativeGap
  refine ⟨τ, y, hData, hCancellation, hReciprocal, ?_⟩
  dsimp only
  rcases hReciprocal.2 with ⟨hSame, hLift⟩ | ⟨hOpp, hLift⟩
  · rcases hGapBranches with ⟨_, hTail⟩ | ⟨hDifferent, _⟩
    · have hPos :
          ∀ᶠ n : ℕ in atTop,
            0 ≤
              (h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ n) (y n)
                - h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ n) (y n)) /
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ n) (y n) := by
        filter_upwards [hTail] with n hn
        exact le_of_lt hn.2.1
      have hEq :
          ∀ᶠ n : ℕ in atTop,
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ n) (y n) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ n) (y n)
              = 1 +
                (h3TerminalOrientedSelectedGradientLogForPair
                    u p sGradient (τ n) (y n)
                  - h3TerminalOrientedSelectedSignedCurlLogForPair
                    u p sGradient (τ n) (y n)) /
                  h3TerminalOrientedSelectedSignedCurlLogForPair
                    u p sGradient (τ n) (y n) := by
        filter_upwards [hTail] with n hn
        exact hn.2.2
      exact Or.inl ⟨hSame,
        positiveGrowth_relativeClusterLift_of_reciprocalLift
          hData hPos hEq hLift⟩
    · exact (hDifferent hSame).elim
  · rcases hGapBranches with ⟨hSame, _⟩ | ⟨_, hTail⟩
    · exact (hOpp hSame).elim
    · have hPos :
          ∀ᶠ n : ℕ in atTop,
            0 ≤
              (h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ n) (y n)
                - h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ n) (y n)) /
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ n) (y n) := by
        filter_upwards [hTail] with n hn
        exact le_of_lt hn.2.1
      have hEq :
          ∀ᶠ n : ℕ in atTop,
            h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ n) (y n) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ n) (y n)
              = 1 +
                (h3TerminalOrientedSelectedSignedCurlLogForPair
                    u p sGradient (τ n) (y n)
                  - h3TerminalOrientedSelectedGradientLogForPair
                    u p sGradient (τ n) (y n)) /
                  h3TerminalOrientedSelectedGradientLogForPair
                    u p sGradient (τ n) (y n) := by
        filter_upwards [hTail] with n hn
        exact hn.2.2
      exact Or.inr ⟨hOpp,
        positiveGrowth_relativeClusterLift_of_reciprocalLift
          hData hPos hEq hLift⟩

end

end Euclidean
end Bridge
end PrimeTensor
