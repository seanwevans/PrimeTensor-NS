import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Finite.Linear

/-!
# Direct superlinear smaller-log growth under relative matching

On a matching subsequence the index-to-smaller-log quotient tends to zero.
Since the smaller log is eventually positive, it eventually exceeds every
fixed positive multiple of the original subsequence index. This direct
growth form applies to the signed curl or selected gradient logarithm,
depending on which is smaller. Matching remains a conditional branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Vanishing index-to-denominator ratio and eventual positivity force
the denominator above every positive multiple of the index. -/
private theorem smaller_eventually_exceeds_index_multiple
    (k : ℕ → ℕ)
    (D : ℕ → ℝ)
    (hDPos : ∀ᶠ n : ℕ in atTop, 0 < D n)
    (hQuotientZero :
      Tendsto (fun n : ℕ => (k n : ℝ) / D n)
        atTop (𝓝 (0 : ℝ)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) < D n := by
  have hSmall :
      ∀ᶠ n : ℕ in atTop,
        (k n : ℝ) / D n < M⁻¹ :=
    hQuotientZero.eventually (Iio_mem_nhds (inv_pos.mpr hM))
  filter_upwards [hDPos, hSmall] with n hn hBound
  have hIndex : (k n : ℝ) < M⁻¹ * D n :=
    (div_lt_iff₀ hn).1 hBound
  calc
    M * (k n : ℝ) < M * (M⁻¹ * D n) :=
      mul_lt_mul_of_pos_left hIndex hM
    _ = D n := by field_simp [ne_of_gt hM]

/-- A gradient-dominant matching tail has signed curl logarithm above
every positive multiple of its original subsequence index. -/
theorem positiveGrowth_gradientMatching_forces_everyLinearSignedCurl
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hMatchingScale :
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
        u a T p sCurl sGradient sComplement τ y)
    (hSame : sComplement = sGradient)
    (hk : StrictMono k)
    (hMatching :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y := hMatchingScale.1.2.1
  have hBPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.2.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hMatchingScale.2 with ⟨_, hRule⟩ | ⟨hOpp, _⟩
  · exact smaller_eventually_exceeds_index_multiple
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      hBPos (hRule k hk hMatching) M hM
  · exact (hOpp hSame).elim

/-- A curl-dominant matching tail has selected gradient logarithm above
every positive multiple of its original subsequence index. -/
theorem positiveGrowth_curlMatching_forces_everyLinearGradient
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    (hMatchingScale :
      H3TerminalPositiveGrowthDominanceMatchingScaleAt
        u a T p sCurl sGradient sComplement τ y)
    (hOpp : sComplement ≠ sGradient)
    (hk : StrictMono k)
    (hMatching :
      Tendsto
        (fun n : ℕ =>
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n))
            - h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
        atTop (𝓝 (0 : ℝ)))
    (M : ℝ)
    (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      M * (k n : ℝ) <
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) := by
  have hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y := hMatchingScale.1.2.1
  have hAPos :
      ∀ᶠ n : ℕ in atTop,
        0 < h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)) :=
    (hRelative.1.comp hk.tendsto_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
  rcases hMatchingScale.2 with ⟨hSame, _⟩ | ⟨_, hRule⟩
  · exact (hOpp hSame).elim
  · exact smaller_eventually_exceeds_index_multiple
      k
      (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ (k n)) (y (k n)))
      hAPos (hRule k hk hMatching) M hM

end

end Euclidean
end Bridge
end PrimeTensor
