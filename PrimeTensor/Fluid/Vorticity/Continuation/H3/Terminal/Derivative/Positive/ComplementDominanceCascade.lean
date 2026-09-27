import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ResolvedComplementCascade

/-!
# Additive dominance in the positive-growth triple native branch

The native complementary logarithm is exactly the selected-gradient logarithm
minus the correctly signed curl logarithm.  In the triple-escape branch, the
fixed complementary orientation therefore determines which of those two large
terms has an additive gap exceeding `n` on the positive-growth sequence.

If the complementary orientation agrees with the selected-gradient
orientation, the selected gradient exceeds the signed curl.  If they differ,
the signed curl exceeds the selected gradient.  Both gaps tend to `+∞` in
their respective branches.  An unbounded additive gap alone does not decide
the ratio of the two diverging terms.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable def h3TerminalOrientedSelectedGradientLogForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient : H3TerminalOrientation)
    (t : ℝ)
    (x : Point3) : ℝ :=
  h3TerminalOrientedValue sGradient
    (PrimeTensor.Bridge.MulReal.logValue
      (h3TerminalNativeGradientForPair u p t x))

noncomputable def h3TerminalOrientedSelectedSignedCurlLogForPair
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient : H3TerminalOrientation)
    (t : ℝ)
    (x : Point3) : ℝ :=
  h3TerminalOrientedValue sGradient
    (h3TerminalSelectedSignedNativeCurlLog u p t x)

/-- Applying one orientation to the exact complementary identity preserves
the signed additive difference. -/
theorem oriented_nativeComplement_eq_orientedGradient_sub_signedCurl
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (s : H3TerminalOrientation)
    (t : ℝ)
    (x : Point3) :
    h3TerminalOrientedValue s
        (PrimeTensor.Bridge.MulReal.logValue
          (h3TerminalNativeComplementGradientForPair u p t x))
      =
    h3TerminalOrientedSelectedGradientLogForPair u p s t x
      -
    h3TerminalOrientedSelectedSignedCurlLogForPair u p s t x := by
  rw [logValue_nativeComplement_eq_gradient_sub_signedCurl]
  cases s <;>
    simp [h3TerminalOrientedSelectedGradientLogForPair,
      h3TerminalOrientedSelectedSignedCurlLogForPair,
      h3TerminalOrientedValue] <;>
    ring

/-- Opposite complementary and selected-gradient orientations reverse the
order of the two terms in the exact additive difference. -/
theorem oriented_nativeComplement_eq_signedCurl_sub_orientedGradient_of_ne
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sComplement sGradient : H3TerminalOrientation)
    (hOpp : sComplement ≠ sGradient)
    (t : ℝ)
    (x : Point3) :
    h3TerminalOrientedValue sComplement
        (PrimeTensor.Bridge.MulReal.logValue
          (h3TerminalNativeComplementGradientForPair u p t x))
      =
    h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient t x
      -
    h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient t x := by
  rw [logValue_nativeComplement_eq_gradient_sub_signedCurl]
  cases sComplement <;> cases sGradient <;>
    simp [h3TerminalOrientedSelectedGradientLogForPair,
      h3TerminalOrientedSelectedSignedCurlLogForPair,
      h3TerminalOrientedValue] at hOpp ⊢ <;>
    ring

/-- The quantitative additive dominance determined by the complementary
escape orientation on one fixed positive-growth time and point sequence. -/
def H3TerminalPositiveGrowthComplementDominanceAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sGradient sComplement : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  (sComplement = sGradient
    ∧
    (∀ n : ℕ,
      (n : ℝ) <
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n)
          -
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
    ∧
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n)
          -
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n))
      atTop atTop)
    ∨
  (sComplement ≠ sGradient
    ∧
    (∀ n : ℕ,
      (n : ℝ) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n)
          -
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
    ∧
    Tendsto
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ n) (y n)
          -
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ n) (y n))
      atTop atTop)

private theorem tendsto_atTop_of_index_lt
    {f : ℕ → ℝ}
    (hf : ∀ n : ℕ, (n : ℝ) < f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCast : (N : ℝ) ≤ n := by exact_mod_cast hn
  exact le_of_lt (lt_trans (lt_of_lt_of_le hN hCast) (hf n))

/-- Triple native escape yields one of two quantitative additive dominance
directions without losing the full positive-growth cascade. -/
theorem positiveGrowth_complementDominance_of_tripleNativeCascade
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
        H3TerminalPositiveGrowthComplementDominanceAt
            u p sGradient sComplement τ y := by
  classical
  obtain ⟨τ, y, hData, hCancellation, hComplementBound,
    _hComplementEscape⟩ := hTriple
  refine ⟨τ, y, hData, hCancellation, ?_⟩
  unfold H3TerminalPositiveGrowthComplementDominanceAt
  by_cases hSame : sComplement = sGradient
  · have hGap :
        ∀ n : ℕ,
          (n : ℝ) <
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ n) (y n)
              -
            h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ n) (y n) := by
      intro n
      have hAt := hComplementBound n
      rw [hSame] at hAt
      rw [oriented_nativeComplement_eq_orientedGradient_sub_signedCurl
        u p sGradient (τ n) (y n)] at hAt
      exact hAt
    exact Or.inl ⟨hSame, hGap, tendsto_atTop_of_index_lt hGap⟩
  · have hGap :
        ∀ n : ℕ,
          (n : ℝ) <
            h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ n) (y n)
              -
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ n) (y n) := by
      intro n
      have hAt := hComplementBound n
      rw [oriented_nativeComplement_eq_signedCurl_sub_orientedGradient_of_ne
        u p sComplement sGradient hSame (τ n) (y n)] at hAt
      exact hAt
    exact Or.inr ⟨hSame, hGap, tendsto_atTop_of_index_lt hGap⟩

end

end Euclidean
end Bridge
end PrimeTensor
