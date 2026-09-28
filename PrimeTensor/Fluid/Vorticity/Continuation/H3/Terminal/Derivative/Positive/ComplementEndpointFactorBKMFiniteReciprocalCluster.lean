import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMFiniteRelativeCluster
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeRateTrichotomy

/-!
# Reciprocal finite relative-rate cluster at the endpoint

Under the endpoint ceilings, the finite dominant ratio cluster has a
positive limit. Its reciprocal smaller-to-dominant ratio converges on the
same strictly increasing native subsequence to the reciprocal of that
limit. The matching case is included when the normalized gap cluster is zero.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The finite cluster from the physical ceilings carries the reciprocal
ratio limit on the identical quantitative native subsequence. -/
theorem positiveGrowth_endpoint_finiteReciprocalCluster_of_exponentialCeiling
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
    ∃ c : ℝ, 0 ≤ c ∧ 0 < (1 + c)⁻¹ ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧
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
              atTop (𝓝 (1 + c)) ∧
            Tendsto (fun n : ℕ =>
              h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n)) /
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
              atTop (𝓝 ((1 + c)⁻¹))) ∨
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
              atTop (𝓝 (1 + c)) ∧
            Tendsto (fun n : ℕ =>
              h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ (k n)) (y (k n)) /
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ (k n)) (y (k n)))
              atTop (𝓝 ((1 + c)⁻¹)))) := by
  obtain ⟨c, hc, k, hkMono, hData', hBranch⟩ :=
    positiveGrowth_endpoint_finiteRelativeCluster_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hCancellation hRelative
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  have hOnePos : (0 : ℝ) < 1 + c := by linarith
  have hInvPos : (0 : ℝ) < (1 + c)⁻¹ := inv_pos.mpr hOnePos
  have hNonzero : (1 + c : ℝ) ≠ 0 := ne_of_gt hOnePos
  refine ⟨c, hc, hInvPos, k, hkMono, hData', ?_⟩
  rcases hBranch with ⟨hSame, hGapLimit, hRatioLimit⟩ |
    ⟨hOpp, hGapLimit, hRatioLimit⟩
  · have hInvLimit :
        Tendsto (fun n : ℕ =>
          (h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))⁻¹)
          atTop (𝓝 ((1 + c)⁻¹)) :=
      hRatioLimit.inv₀ hNonzero
    have hReciprocalLimit :
        Tendsto (fun n : ℕ =>
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))
          atTop (𝓝 ((1 + c)⁻¹)) := by
      have hFunction :
          (fun n : ℕ =>
            h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n))) =
          (fun n : ℕ =>
            (h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)))⁻¹) := by
        funext n
        simp only [inv_div]
      rw [hFunction]
      exact hInvLimit
    exact Or.inl ⟨hSame, hGapLimit, hRatioLimit, hReciprocalLimit⟩
  · have hInvLimit :
        Tendsto (fun n : ℕ =>
          (h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)))⁻¹)
          atTop (𝓝 ((1 + c)⁻¹)) :=
      hRatioLimit.inv₀ hNonzero
    have hReciprocalLimit :
        Tendsto (fun n : ℕ =>
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
          atTop (𝓝 ((1 + c)⁻¹)) := by
      have hFunction :
          (fun n : ℕ =>
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n))) =
          (fun n : ℕ =>
            (h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)))⁻¹) := by
        funext n
        simp only [inv_div]
      rw [hFunction]
      exact hInvLimit
    exact Or.inr ⟨hOpp, hGapLimit, hRatioLimit, hReciprocalLimit⟩

end

end Euclidean
end Bridge
end PrimeTensor
