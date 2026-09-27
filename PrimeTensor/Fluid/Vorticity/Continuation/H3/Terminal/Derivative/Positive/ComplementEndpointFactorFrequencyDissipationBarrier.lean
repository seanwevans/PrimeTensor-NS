import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorFrequencyExponentialBarrier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.CharacteristicFrequencyAmplitudeCorridor

/-!
# Dissipation ratio on the exponential frequency branch

The existing tail estimate bounds the characteristic-frequency square
by a fixed anchor coefficient times full H³ dissipation divided by H³
energy. On the persistent frequency branch this forces an exponential
square-root-index lower bound for that normalized dissipation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The frequency square is eventually controlled by the full
dissipation-to-energy ratio along any quantitative native witness. -/
theorem positiveGrowth_nativeWitness_frequencySq_le_dissipationRatio
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hNative :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y) :
    ∀ᶠ n : ℕ in atTop,
      h3TopCharacteristicFrequencyAt u (τ n) ^ 2 ≤
        (4 + 3 * velocityH3Energy0At u b) *
          (velocityH3DissipationAt u (τ n) /
            velocityH3EnergyAt u (τ n)) := by
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hCPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
    linarith
  have hUpperEventually : ∀ᶠ t : ℝ in 𝓝[<] T,
      velocityH3EnergyAt u t ≤
        (4 + 3 * velocityH3Energy0At u b) *
          velocityH3Energy3At u t :=
    eventually_velocityH3EnergyAt_le_anchorCoefficient_mul_energy3_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  obtain ⟨c, hc, hUpper⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset).1 hUpperEventually
  obtain ⟨hAt, hTau, _, _, _, _, _, _, _⟩ := hNative
  have hLate : ∀ᶠ n : ℕ in atTop, c < τ n :=
    (tendsto_order.1 hTau).1 c hc
  filter_upwards [hLate] with n hn
  have hAtTail : τ n ∈ Set.Ioo c T :=
    ⟨hn, (hAt n).1.2⟩
  exact
    h3TopCharacteristicFrequencyAt_sq_le_coefficient_mul_dissipation_div_energy
      hCPos (hUpper hAtTail)

/-- Relative escape preserves the native cascade and ratio condition.
Either the normalized vorticity factor diverges, or every fixed
exponential square-root-index frequency scale has its square bounded
above by the anchored full dissipation-to-energy ratio. -/
theorem endpointFactor_relativeRefinedWitness_dissipationExponentialBarrier
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
    (hWitness :
      H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio) :
    ∃ l : ℕ → ℕ,
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l n))) (fun n => y (k (l n))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l n)) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l n)))|) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop ∨
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              (velocityH3DissipationAt u (τ (k (l n))) /
                velocityH3EnergyAt u (τ (k (l n)))))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_frequencyExponentialBarrier
      hH3 hNoExtension hClass hb hWitness
  have hFrequencySq :=
    positiveGrowth_nativeWitness_frequencySq_le_dissipationRatio
      hH3 hNoExtension hClass hb hNative
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hBarrier with hVorticity | hFrequency
  · exact Or.inl hVorticity
  · refine Or.inr ?_
    intro M hM
    filter_upwards [hFrequency M hM, hFrequencySq] with n hn hnSq
    have hExpNonneg :
        0 ≤ Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) :=
      le_of_lt (Real.exp_pos _)
    have hExpSq :
        Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 ≤
          h3TopCharacteristicFrequencyAt u (τ (k (l n))) ^ 2 :=
      pow_le_pow_left₀ hExpNonneg hn 2
    exact hExpSq.trans hnSq

end

end Euclidean
end Bridge
end PrimeTensor
