import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Frequency.Log

/-!
# Endpoint factor alternative in characteristic-frequency form

The amplitude corridor transfers the persistent logarithmic H³-energy
factor rate to an explicit characteristic-frequency logarithm on the
same quantitative native relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem squaredRate_of_eventually_le
    (k : ℕ → ℕ) (L F : ℕ → ℝ)
    (hRate : Tendsto (fun n : ℕ => L n ^ 2 / ((k n : ℝ) + 1)) atTop atTop)
    (hLE : ∀ᶠ n : ℕ in atTop, L n ≤ F n)
    (hLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ L n) :
    Tendsto (fun n : ℕ => F n ^ 2 / ((k n : ℝ) + 1)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [hRate.eventually (eventually_ge_atTop C), hLE, hLNonneg]
    with n hn hBound hNonneg
  have hSquare : L n ^ 2 ≤ F n ^ 2 :=
    (sq_le_sq₀ hNonneg (hNonneg.trans hBound)).2 hBound
  exact hn.trans (div_le_div_of_nonneg_right hSquare (by positivity))

/-- On the refined relative-escape witness, the persistent endpoint
factor rate is carried either by vorticity or by the logarithm of the
characteristic-frequency amplitude bound. The native cascade and the
relative-ratio lower bound use those very same indices. -/
theorem endpointFactor_relativeRefinedWitness_frequencyRateAlternative
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
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log
              ((4 + 3 * velocityH3Energy0At u b) *
                (velocityH3Energy0At u b + 1) *
                h3TopCharacteristicFrequencyAt u (τ (k (l n))) ^ 6)) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop) := by
  obtain ⟨l, hNative, hRatio, hRate, hUpper⟩ :=
    endpointFactor_relativeRefinedWitness_logEnergy_le_frequencyLog
      hH3 hNoExtension hClass hb hWitness
  have hEnergy : Tendsto
      (fun n : ℕ => velocityH3EnergyAt u (τ (k (l n)))) atTop atTop := by
    rcases hNative with ⟨_, _, hEnergy, _, _, _, _, _, _⟩
    exact hEnergy
  have hLogNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 + Real.log (velocityH3EnergyAt u (τ (k (l n)))) := by
    filter_upwards [hEnergy.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn
    have hnLog := Real.log_nonneg hn
    linarith
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hRate with hVorticity | hLogEnergy
  · exact Or.inl hVorticity
  · exact Or.inr
      (squaredRate_of_eventually_le (fun n => k (l n))
        (fun n => 1 + Real.log (velocityH3EnergyAt u (τ (k (l n)))))
        (fun n => 1 + Real.log
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3Energy0At u b + 1) *
            h3TopCharacteristicFrequencyAt u (τ (k (l n))) ^ 6))
        hLogEnergy hUpper hLogNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
