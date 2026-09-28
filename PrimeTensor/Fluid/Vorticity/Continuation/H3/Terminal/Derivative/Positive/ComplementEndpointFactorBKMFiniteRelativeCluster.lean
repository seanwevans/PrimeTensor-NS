import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNormalizedLogGap
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeClusterCascade

/-!
# Finite relative-log cluster under endpoint physical ceilings

The positive normalized gap in the dominant relative branch is eventually
bounded under the physical ceilings. Compactness extracts a finite
nonnegative cluster value, and the exact gap identity transfers it to the
dominant-to-smaller logarithmic ratio. The quantitative native witness
survives the same extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An eventually nonnegative and bounded gap has a finite cluster; an
eventual exact ratio identity transfers that limit to the same indices. -/
theorem finite_ratio_cluster_of_positive_bounded_gap
    (gap ratio : ℕ → ℝ)
    (C : ℝ)
    (hPos : ∀ᶠ n : ℕ in atTop, 0 ≤ gap n)
    (hBound : ∀ᶠ n : ℕ in atTop, gap n ≤ C)
    (hEq : ∀ᶠ n : ℕ in atTop, ratio n = 1 + gap n) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ k : ℕ → ℕ, StrictMono k ∧
      Tendsto (fun n : ℕ => gap (k n)) atTop (𝓝 c) ∧
      Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c)) := by
  have hInInterval :
      ∀ᶠ n : ℕ in atTop, gap n ∈ Set.Icc (0 : ℝ) C := by
    filter_upwards [hPos, hBound] with n hn hCeiling
    exact ⟨hn, hCeiling⟩
  obtain ⟨c, hc, k, hkMono, hGapLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).tendsto_subseq'
      hInInterval.frequently
  have hkTop : Tendsto k atTop atTop := hkMono.tendsto_atTop
  have hEqK : ∀ᶠ n : ℕ in atTop,
      ratio (k n) = 1 + gap (k n) := hkTop.eventually hEq
  have hAddLimit :
      Tendsto (fun n : ℕ => 1 + gap (k n)) atTop (𝓝 (1 + c)) :=
    hGapLimit.const_add 1
  have hRatioLimit :
      Tendsto (fun n : ℕ => ratio (k n)) atTop (𝓝 (1 + c)) := by
    have hEqK' : ∀ᶠ n : ℕ in atTop,
        1 + gap (k n) = ratio (k n) := by
      filter_upwards [hEqK] with n hn
      exact hn.symm
    exact hAddLimit.congr' hEqK'
  exact ⟨c, hc.1, k, hkMono, hGapLimit, hRatioLimit⟩

/-- A cancellation-compatible relative-gap witness with the three endpoint
ceilings has a finite nonnegative dominant relative-rate cluster on one
strictly increasing native subsequence. -/
theorem positiveGrowth_endpoint_finiteRelativeCluster_of_exponentialCeiling
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
    ∃ c : ℝ, 0 ≤ c ∧ ∃ k : ℕ → ℕ, StrictMono k ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k n)) (fun n => y (k n)) ∧
      ((sComplement = sGradient ∧
          Tendsto (fun n : ℕ =>
            (h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)) -
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n))) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n))) atTop (𝓝 c) ∧
          Tendsto (fun n : ℕ =>
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (1 + c))) ∨
       (sComplement ≠ sGradient ∧
          Tendsto (fun n : ℕ =>
            (h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)) -
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n))) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n))) atTop (𝓝 c) ∧
          Tendsto (fun n : ℕ =>
            h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)))
            atTop (𝓝 (1 + c)))) := by
  obtain ⟨L, _, N, hAbsBound⟩ :=
    positiveGrowth_endpoint_normalizedLogGaps_bounded_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hCancellation
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
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
    exact hAbsBound i hi
  rcases hRelative.2.2 with ⟨hSame, hTail⟩ | ⟨hOpp, hTail⟩
  · have hPos : ∀ᶠ i : ℕ in atTop,
        0 ≤ (h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i) := by
      filter_upwards [hTail] with i hi
      exact le_of_lt hi.2.1
    have hBound : ∀ᶠ i : ℕ in atTop,
        (h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i) ≤ L := by
      filter_upwards [hEventuallyBound] with i hi
      exact (le_abs_self _).trans hi.1
    have hEq : ∀ᶠ i : ℕ in atTop,
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i) =
          1 + (h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) := by
      filter_upwards [hTail] with i hi
      exact hi.2.2
    obtain ⟨c, hc, k, hkMono, hGapLimit, hRatioLimit⟩ :=
      finite_ratio_cluster_of_positive_bounded_gap
        (fun i => (h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ i) (y i))
        (fun i => h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i))
        L hPos hBound hEq
    have hData' := positiveGrowth_quantitativeNativeData_comp_cofinal
      hData (fun n => hkMono.le_apply)
    exact ⟨c, hc, k, hkMono, hData', Or.inl ⟨hSame, hGapLimit, hRatioLimit⟩⟩
  · have hPos : ∀ᶠ i : ℕ in atTop,
        0 ≤ (h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i) := by
      filter_upwards [hTail] with i hi
      exact le_of_lt hi.2.1
    have hBound : ∀ᶠ i : ℕ in atTop,
        (h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i) ≤ L := by
      filter_upwards [hEventuallyBound] with i hi
      exact (le_abs_self _).trans hi.2
    have hEq : ∀ᶠ i : ℕ in atTop,
        h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i) =
          1 + (h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ i) (y i) -
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ i) (y i)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i) := by
      filter_upwards [hTail] with i hi
      exact hi.2.2
    obtain ⟨c, hc, k, hkMono, hGapLimit, hRatioLimit⟩ :=
      finite_ratio_cluster_of_positive_bounded_gap
        (fun i => (h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ i) (y i) -
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ i) (y i)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ i) (y i))
        (fun i => h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i))
        L hPos hBound hEq
    have hData' := positiveGrowth_quantitativeNativeData_comp_cofinal
      hData (fun n => hkMono.le_apply)
    exact ⟨c, hc, k, hkMono, hData', Or.inr ⟨hOpp, hGapLimit, hRatioLimit⟩⟩

end

end Euclidean
end Bridge
end PrimeTensor
