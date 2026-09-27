import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeMatchingBothLogs

/-!
# Both oriented logs have linear lower scale at a positive finite rate

A positive finite normalized-gap cluster `c` forces the smaller oriented
log above `k(n) / (c + ε)` eventually. The indexed additive gap makes the
dominant log larger still. Both inequalities hold on the same extracted
time and point subsequence for either complementary orientation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Transfer a positive linear lower bound from the smaller quantity to
the larger one using the indexed positive additive gap. -/
private theorem both_logs_above_finite_scale
    (W L : ℕ → ℝ)
    (k : ℕ → ℕ)
    (c ε : ℝ)
    (hc : 0 < c)
    (hε : 0 < ε)
    (hGap : ∀ n : ℕ, (k n : ℝ) < W n - L n)
    (hSmaller :
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) < (c + ε) * L n) :
    ∀ᶠ n : ℕ in atTop,
      (k n : ℝ) < (c + ε) * L n
        ∧
      (k n : ℝ) < (c + ε) * W n := by
  filter_upwards [hSmaller] with n hn
  have hIndexNonneg : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg _
  have hDominant : L n < W n := by
    linarith [hGap n]
  have hScaled : (c + ε) * L n < (c + ε) * W n :=
    mul_lt_mul_of_pos_left hDominant (add_pos hc hε)
  exact ⟨hn, hn.trans hScaled⟩

/-- Gradient-dominant finite separation makes both oriented logs grow at
least linearly with the original subsequence index. -/
theorem positiveGrowth_gradientFiniteRate_forces_bothLogsLinear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hScale :
      H3TerminalPositiveGrowthDominanceScaleClassificationAt
        u a T p sCurl sGradient sComplement τ y)
    (hSame : sComplement = sGradient)
    (hk : StrictMono k)
    (hc : 0 < c)
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
      (k n : ℝ) <
          (c + ε) *
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
        ∧
      (k n : ℝ) <
          (c + ε) *
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) := by
  have hSmaller :=
    positiveGrowth_gradientFiniteRate_forces_linearSignedCurl
      hScale hSame hk hFinite hε
  rcases hScale.1.1.1 with ⟨_, hGap, _⟩ | ⟨hOpp, _, _⟩
  · have hBoth := both_logs_above_finite_scale
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      k c ε hc hε (fun n => hGap (k n)) hSmaller
    filter_upwards [hBoth] with n hn
    exact ⟨hn.2, hn.1⟩
  · exact (hOpp hSame).elim

/-- Curl-dominant finite separation makes both oriented logs grow at
least linearly with the original subsequence index. -/
theorem positiveGrowth_curlFiniteRate_forces_bothLogsLinear
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {c ε : ℝ}
    (hScale :
      H3TerminalPositiveGrowthDominanceScaleClassificationAt
        u a T p sCurl sGradient sComplement τ y)
    (hOpp : sComplement ≠ sGradient)
    (hk : StrictMono k)
    (hc : 0 < c)
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
      (k n : ℝ) <
          (c + ε) *
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
        ∧
      (k n : ℝ) <
          (c + ε) *
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) := by
  have hSmaller :=
    positiveGrowth_curlFiniteRate_forces_linearGradient
      hScale hOpp hk hFinite hε
  rcases hScale.1.1.1 with ⟨hSame, _, _⟩ | ⟨_, hGap, _⟩
  · exact (hOpp hSame).elim
  · exact both_logs_above_finite_scale
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      k c ε hc hε (fun n => hGap (k n)) hSmaller

end

end Euclidean
end Bridge
end PrimeTensor
