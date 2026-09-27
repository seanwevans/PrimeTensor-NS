import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorFrequencySqrtBarrier

/-!
# Exponential frequency barrier on relative escape

The intrinsic logarithmic frequency branch forces the characteristic
frequency eventually above every fixed exponential square-root-index
scale. The vorticity-rate branch and the native ratio witness are
retained without changing indices.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem eventual_exponentialFrequency_of_sqrtLogBarrier
    (k : ℕ → ℕ) (Λ : ℕ → ℝ)
    (hΛTop : Tendsto Λ atTop atTop)
    (hBarrier : ∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
      M * Real.sqrt ((k n : ℝ) + 1) ≤ 1 + Real.log (Λ n))
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (M * Real.sqrt ((k n : ℝ) + 1)) ≤ Λ n := by
  have hLarger : 0 ≤ M + 1 := by linarith
  filter_upwards
      [hBarrier (M + 1) hLarger,
        hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hΛOne
  have hDenOne : 1 ≤ (k n : ℝ) + 1 := by
    have hnNonneg : 0 ≤ (k n : ℝ) := Nat.cast_nonneg _
    linarith
  have hSqrtOne : 1 ≤ Real.sqrt ((k n : ℝ) + 1) := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hDenOne)
  have hLogLower :
      M * Real.sqrt ((k n : ℝ) + 1) ≤ Real.log (Λ n) := by
    nlinarith
  calc
    Real.exp (M * Real.sqrt ((k n : ℝ) + 1))
        ≤ Real.exp (Real.log (Λ n)) :=
          Real.exp_le_exp.mpr hLogLower
    _ = Λ n := Real.exp_log (by linarith)

/-- On the frequency branch, the intrinsic characteristic frequency
eventually exceeds `exp (M * sqrt (original index + 1))` for every
fixed nonnegative `M`; otherwise the normalized vorticity factor
diverges on the same native relative-escape witness. -/
theorem endpointFactor_relativeRefinedWitness_frequencyExponentialBarrier
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
          Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ≤
            h3TopCharacteristicFrequencyAt u (τ (k (l n))))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_frequencySqrtBarrier
      hH3 hNoExtension hClass hb hWitness
  have hΛTop : Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ (k (l n))))
      atTop atTop := by
    rcases hNative with ⟨_, _, _, _, _, hΛTop, _, _, _⟩
    exact hΛTop
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hBarrier with hVorticity | hFrequency
  · exact Or.inl hVorticity
  · exact Or.inr (fun M hM =>
      eventual_exponentialFrequency_of_sqrtLogBarrier
        (fun n => k (l n))
        (fun n => h3TopCharacteristicFrequencyAt u (τ (k (l n))))
        hΛTop hFrequency M hM)

end

end Euclidean
end Bridge
end PrimeTensor
