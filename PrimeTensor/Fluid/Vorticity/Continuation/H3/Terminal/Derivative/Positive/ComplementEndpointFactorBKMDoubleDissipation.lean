import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMTwoBranch
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorTransportExcessBarrier

/-!
# Double-exponential dissipation and transport consequences

The double-exponential characteristic-frequency branch forces the
same scale in full dissipation divided by H³ energy and in the
positive-growth adverse transport excess. Both controls hold on the
same refined native relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Either the normalized vorticity factor diverges, or the squared
double-exponential frequency scale is bounded above by both anchored
normalized dissipation and anchored adverse transport excess. -/
theorem endpointFactor_relativeRefinedWitness_BKMDoubleDissipation
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    {ratio : ℕ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l q : ℕ → ℕ,
      (∀ n : ℕ, n ≤ q n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q n)))) (fun n => y (k (l (q n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (q n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (q n))))|) ^ 2 /
              ((k (l (q n)) : ℝ) + 1))
          atTop atTop ∨
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              (velocityH3DissipationAt u (τ (k (l (q n)))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) ∧
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              h3PathTransportExcessRate u (τ (k (l (q n)))))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMTwoBranch
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hFrequency
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inl hVorticity⟩
  have hFrequencySq :=
    positiveGrowth_nativeWitness_frequencySq_le_dissipationRatio
      hH3 hNoExtension hClass hb hNative
  have hDLe :=
    positiveGrowth_nativeWitness_dissipationRatio_le_transportExcess
      hH3 hClass hb hNative
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCNonneg : 0 ≤ 4 + 3 * velocityH3Energy0At u b := by
    linarith
  refine ⟨l, q, hqIndex, hNative, hRatio, Or.inr ?_⟩
  intro M hM
  filter_upwards [hFrequency M hM, hFrequencySq] with n hn hnSq
  have hExpNonneg : 0 ≤ Real.exp
      (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
        (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) :=
    le_of_lt (Real.exp_pos _)
  have hExpSq :
      Real.exp
        (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
          (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2 ≤
        h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))) ^ 2 :=
    pow_le_pow_left₀ hExpNonneg hn 2
  have hDissipation := hExpSq.trans hnSq
  exact ⟨hDissipation,
    hDissipation.trans
      (mul_le_mul_of_nonneg_left (hDLe n) hCNonneg)⟩

end

end Euclidean
end Bridge
end PrimeTensor
