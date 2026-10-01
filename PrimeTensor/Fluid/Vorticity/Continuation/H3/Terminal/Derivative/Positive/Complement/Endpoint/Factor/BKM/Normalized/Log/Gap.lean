import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Ratio.Comparability
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Relative.Gap.Cascade

/-!
# Bounded normalized selected-log gaps at the endpoint

Two-sided comparability of positive selected logarithms bounds both
orientations of their additive difference after division by the smaller
logarithm. In a relative-gap branch the corresponding normalized difference
is positive as well as eventually bounded.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Mutual comparability of positive sequences bounds both normalized
additive gaps by one eventual constant. -/
theorem normalized_gaps_bounded_of_eventual_comparability
    (A B : ℕ → ℝ)
    (hAPos : ∀ i : ℕ, 0 < A i)
    (hBPos : ∀ i : ℕ, 0 < B i)
    (hCompare : ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ i : ℕ, N ≤ i → A i ≤ K * B i ∧ B i ≤ K * A i) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      |(A i - B i) / B i| ≤ L ∧
      |(B i - A i) / A i| ≤ L := by
  obtain ⟨K, hKPos, N, hCompare⟩ := hCompare
  refine ⟨K + 1, by linarith, N, ?_⟩
  intro i hi
  have hA := hAPos i
  have hB := hBPos i
  have hAB : A i / B i ≤ K :=
    (div_le_iff₀ hB).2 (hCompare i hi).1
  have hBA : B i / A i ≤ K :=
    (div_le_iff₀ hA).2 (hCompare i hi).2
  have hABNonneg : 0 ≤ A i / B i := le_of_lt (div_pos hA hB)
  have hBANonneg : 0 ≤ B i / A i := le_of_lt (div_pos hB hA)
  have hEqAB : (A i - B i) / B i = A i / B i - 1 := by
    field_simp [ne_of_gt hB] <;> ring
  have hEqBA : (B i - A i) / A i = B i / A i - 1 := by
    field_simp [ne_of_gt hA] <;> ring
  constructor
  · rw [hEqAB]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hEqBA]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The physical ceilings give a common eventual bound for both normalized
selected-log differences on a cancellation-compatible native sequence. -/
theorem positiveGrowth_endpoint_normalizedLogGaps_bounded_of_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      |(h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i) -
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i)) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i)| ≤ L ∧
      |(h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i) -
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i)) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i)| ≤ L := by
  have hCompare :=
    positiveGrowth_endpoint_selectedLogs_comparable_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hCancellation
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  have hGradientPos : ∀ i : ℕ,
      0 < h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ i) (y i) := by
    intro i
    have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact lt_of_le_of_lt hiNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation i).1
  have hCurlPos : ∀ i : ℕ,
      0 < h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ i) (y i) := by
    intro i
    have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact lt_of_le_of_lt hiNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation i).2
  exact normalized_gaps_bounded_of_eventual_comparability
    (fun i => h3TerminalOrientedSelectedGradientLogForPair
      u p sGradient (τ i) (y i))
    (fun i => h3TerminalOrientedSelectedSignedCurlLogForPair
      u p sGradient (τ i) (y i))
    hGradientPos hCurlPos hCompare

/-- A relative-gap witness identifies the positive normalized gap; the
endpoint ceilings also bound that gap above by a constant. -/
theorem positiveGrowth_endpoint_relativeLogGap_positive_bounded_of_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hRelative :
      H3TerminalPositiveGrowthRelativeGapAt
        u p sGradient sComplement τ y)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ((sComplement = sGradient ∧
        ∀ᶠ i : ℕ in atTop,
          0 < (h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) ∧
          (h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) ≤ L) ∨
       (sComplement ≠ sGradient ∧
        ∀ᶠ i : ℕ in atTop,
          0 < (h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) ∧
          (h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) ≤ L)) := by
  obtain ⟨L, hLNonneg, N, hBound⟩ :=
    positiveGrowth_endpoint_normalizedLogGaps_bounded_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hCancellation
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  refine ⟨L, hLNonneg, ?_⟩
  have hEventuallyBound : ∀ᶠ i : ℕ in atTop,
      |(h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i) -
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i)) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i)| ≤ L ∧
      |(h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i) -
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i)) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i)| ≤ L := by
    filter_upwards [eventually_ge_atTop N] with i hi
    exact hBound i hi
  rcases hRelative.2.2 with ⟨hSame, hPositive⟩ | ⟨hOpp, hPositive⟩
  · refine Or.inl ⟨hSame, ?_⟩
    filter_upwards [hPositive, hEventuallyBound] with i hiPos hiBound
    exact ⟨hiPos.2.1, (le_abs_self _).trans hiBound.1⟩
  · refine Or.inr ⟨hOpp, ?_⟩
    filter_upwards [hPositive, hEventuallyBound] with i hiPos hiBound
    exact ⟨hiPos.2.1, (le_abs_self _).trans hiBound.2⟩

end

end Euclidean
end Bridge
end PrimeTensor
