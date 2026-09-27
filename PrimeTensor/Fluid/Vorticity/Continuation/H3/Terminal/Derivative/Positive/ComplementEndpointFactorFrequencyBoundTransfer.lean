import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorFrequencyRate

/-!
# Conditional bounds for the characteristic-frequency factor

The frequency-rate alternative is persistent on a quantitative native
relative-escape witness. An eventual upper bound for either normalized
factor selects divergence of the other one on that same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem frequencyBoundConsequences_of_rate
    (V F : ℕ → ℝ)
    (hRate : Tendsto V atTop atTop ∨ Tendsto F atTop atTop) :
    H3TerminalEndpointFactorBoundConsequences V F := by
  constructor
  · rintro ⟨C, hBound⟩
    rcases hRate with hV | hF
    · exact hV
    · obtain ⟨n, hnLarge, hnBound⟩ :=
        ((hF.eventually (eventually_gt_atTop C)).and hBound).exists
      exact False.elim ((not_lt_of_ge hnBound) hnLarge)
  · rintro ⟨C, hBound⟩
    rcases hRate with hV | hF
    · obtain ⟨n, hnLarge, hnBound⟩ :=
        ((hV.eventually (eventually_gt_atTop C)).and hBound).exists
      exact False.elim ((not_lt_of_ge hnBound) hnLarge)
    · exact hF

/-- A bounded normalized characteristic-frequency logarithm forces
the squared vorticity factor to diverge. Conversely, a bounded
normalized vorticity factor forces divergence of the squared
characteristic-frequency logarithm. Both implications retain the
same native cascade and relative-ratio indices. -/
theorem endpointFactor_relativeRefinedWitness_frequencyBoundConsequences
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
      H3TerminalEndpointFactorBoundConsequences
        (fun n : ℕ =>
          (1 + |g (τ (k (l n)))|) ^ 2 /
            ((k (l n) : ℝ) + 1))
        (fun n : ℕ =>
          (1 + Real.log
            ((4 + 3 * velocityH3Energy0At u b) *
              (velocityH3Energy0At u b + 1) *
              h3TopCharacteristicFrequencyAt u (τ (k (l n))) ^ 6)) ^ 2 /
            ((k (l n) : ℝ) + 1)) := by
  obtain ⟨l, hNative, hRatio, hRate⟩ :=
    endpointFactor_relativeRefinedWitness_frequencyRateAlternative
      hH3 hNoExtension hClass hb hWitness
  exact ⟨l, hNative, hRatio,
    frequencyBoundConsequences_of_rate _ _ hRate⟩

end

end Euclidean
end Bridge
end PrimeTensor
