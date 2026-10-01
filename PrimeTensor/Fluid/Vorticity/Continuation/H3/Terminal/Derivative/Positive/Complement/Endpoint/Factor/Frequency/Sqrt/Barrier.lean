import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Intrinsic.Frequency.Rate

/-!
# Square-root index barrier on the intrinsic frequency branch

The squared intrinsic logarithmic frequency rate supplies an explicit
eventual inequality against every fixed multiple of the square root
of the original extraction index. The vorticity branch remains the
other persistent alternative on the same native witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem eventual_sqrtIndex_bound_of_squareRate
    (k : ℕ → ℕ) (F : ℕ → ℝ)
    (hRate : Tendsto
      (fun n : ℕ => F n ^ 2 / ((k n : ℝ) + 1)) atTop atTop)
    (hFNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ F n)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      M * Real.sqrt ((k n : ℝ) + 1) ≤ F n := by
  filter_upwards
      [hRate.eventually (eventually_ge_atTop (M ^ 2)), hFNonneg]
    with n hn hFn
  have hDenPos : 0 < (k n : ℝ) + 1 := by positivity
  have hSquareBound :
      M ^ 2 * ((k n : ℝ) + 1) ≤ F n ^ 2 :=
    (le_div_iff₀ hDenPos).1 hn
  have hSqrtNonneg : 0 ≤ Real.sqrt ((k n : ℝ) + 1) :=
    Real.sqrt_nonneg _
  have hProdNonneg :
      0 ≤ M * Real.sqrt ((k n : ℝ) + 1) :=
    mul_nonneg hM hSqrtNonneg
  have hProductSquare :
      (M * Real.sqrt ((k n : ℝ) + 1)) ^ 2 ≤ F n ^ 2 := by
    calc
      _ = M ^ 2 * ((k n : ℝ) + 1) := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hDenPos)]
      _ ≤ F n ^ 2 := hSquareBound
  exact (sq_le_sq₀ hProdNonneg hFn).1 hProductSquare

/-- On a single quantitative native relative-escape witness, either
the normalized vorticity factor diverges or the intrinsic frequency
logarithm eventually exceeds every nonnegative multiple of the
square root of the original index. -/
theorem endpointFactor_relativeRefinedWitness_frequencySqrtBarrier
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
          M * Real.sqrt ((k (l n) : ℝ) + 1) ≤
            1 + Real.log
              (h3TopCharacteristicFrequencyAt u (τ (k (l n)))))) := by
  obtain ⟨l, hNative, hRatio, hRate⟩ :=
    endpointFactor_relativeRefinedWitness_intrinsicFrequencyRateAlternative
      hH3 hNoExtension hClass hb hWitness
  have hΛTop : Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ (k (l n))))
      atTop atTop := by
    rcases hNative with ⟨_, _, _, _, _, hΛTop, _, _, _⟩
    exact hΛTop
  have hLogNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 + Real.log
        (h3TopCharacteristicFrequencyAt u (τ (k (l n)))) := by
    filter_upwards [hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hn
    have hnLog := Real.log_nonneg hn
    linarith
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hRate with hVorticity | hFrequency
  · exact Or.inl hVorticity
  · exact Or.inr (fun M hM =>
      eventual_sqrtIndex_bound_of_squareRate (fun n => k (l n))
        (fun n => 1 + Real.log
          (h3TopCharacteristicFrequencyAt u (τ (k (l n)))))
        hFrequency hLogNonneg M hM)

end

end Euclidean
end Bridge
end PrimeTensor
