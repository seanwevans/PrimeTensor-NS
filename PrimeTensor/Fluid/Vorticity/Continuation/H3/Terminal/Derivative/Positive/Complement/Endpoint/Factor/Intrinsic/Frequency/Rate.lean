import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Frequency.Bound.Transfer

/-!
# Intrinsic characteristic-frequency factor on relative escape

The fixed energy anchor in the frequency corridor does not alter a
divergent normalized logarithmic square rate. This file replaces the
anchored logarithm by the characteristic frequency's own logarithm
while retaining the quantitative native relative-escape witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem intrinsicFrequencyRate_of_anchoredRate
    (k : ℕ → ℕ) (Λ : ℕ → ℝ) (A : ℝ)
    (hAOne : 1 ≤ A)
    (hΛTop : Tendsto Λ atTop atTop)
    (hRate : Tendsto
      (fun n : ℕ => (1 + Real.log (A * Λ n ^ 6)) ^ 2 /
        ((k n : ℝ) + 1)) atTop atTop) :
    Tendsto
      (fun n : ℕ => (1 + Real.log (Λ n)) ^ 2 /
        ((k n : ℝ) + 1)) atTop atTop := by
  let C : ℝ := A + 7
  have hCPos : 0 < C := by
    dsimp [C]
    linarith
  have hC2Pos : 0 < C ^ 2 := pow_pos hCPos 2
  have hScale : ∀ᶠ n : ℕ in atTop,
      0 ≤ 1 + Real.log (A * Λ n ^ 6) ∧
      0 ≤ 1 + Real.log (Λ n) ∧
      1 + Real.log (A * Λ n ^ 6) ≤ C * (1 + Real.log (Λ n)) := by
    filter_upwards [hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hnOne
    have hAPos : 0 < A := by linarith
    have hΛPos : 0 < Λ n := by linarith
    have hΛPowPos : 0 < Λ n ^ 6 := pow_pos hΛPos 6
    have hExpand : Real.log (A * Λ n ^ 6) =
        Real.log A + 6 * Real.log (Λ n) := by
      rw [Real.log_mul (ne_of_gt hAPos) (ne_of_gt hΛPowPos),
        Real.log_pow]
      norm_num
    have hLogA : 0 ≤ Real.log A := Real.log_nonneg hAOne
    have hLogΛ : 0 ≤ Real.log (Λ n) := Real.log_nonneg hnOne
    have hLogAUpper : Real.log A ≤ A :=
      Real.log_le_self (le_of_lt hAPos)
    constructor
    · rw [hExpand]
      linarith
    constructor
    · linarith
    · rw [hExpand]
      dsimp only [C]
      have hExtra : 0 ≤ (A + 1) * Real.log (Λ n) :=
        mul_nonneg (by linarith) hLogΛ
      nlinarith
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards
      [hRate.eventually (eventually_ge_atTop (C ^ 2 * max M 0)), hScale]
    with n hn ⟨hFNonneg, hGNonneg, hBound⟩
  have hScaledNonneg : 0 ≤ C * (1 + Real.log (Λ n)) :=
    mul_nonneg (le_of_lt hCPos) hGNonneg
  have hSquares :
      (1 + Real.log (A * Λ n ^ 6)) ^ 2 ≤
        C ^ 2 * (1 + Real.log (Λ n)) ^ 2 := by
    calc
      _ ≤ (C * (1 + Real.log (Λ n))) ^ 2 :=
        (sq_le_sq₀ hFNonneg hScaledNonneg).2 hBound
      _ = C ^ 2 * (1 + Real.log (Λ n)) ^ 2 := by ring
  have hDiv :
      (1 + Real.log (A * Λ n ^ 6)) ^ 2 / ((k n : ℝ) + 1) ≤
        C ^ 2 * ((1 + Real.log (Λ n)) ^ 2 / ((k n : ℝ) + 1)) := by
    calc
      _ ≤ (C ^ 2 * (1 + Real.log (Λ n)) ^ 2) /
          ((k n : ℝ) + 1) :=
        div_le_div_of_nonneg_right hSquares (by positivity)
      _ = C ^ 2 * ((1 + Real.log (Λ n)) ^ 2 /
          ((k n : ℝ) + 1)) := by ring
  have hScaledBound :
      C ^ 2 * M ≤
        C ^ 2 * ((1 + Real.log (Λ n)) ^ 2 / ((k n : ℝ) + 1)) := by
    calc
      _ ≤ C ^ 2 * max M 0 :=
        mul_le_mul_of_nonneg_left (le_max_left M 0) (le_of_lt hC2Pos)
      _ ≤ (1 + Real.log (A * Λ n ^ 6)) ^ 2 /
          ((k n : ℝ) + 1) := hn
      _ ≤ _ := hDiv
  by_contra hNot
  have hStrict :
      (1 + Real.log (Λ n)) ^ 2 / ((k n : ℝ) + 1) < M :=
    lt_of_not_ge hNot
  exact (not_lt_of_ge hScaledBound)
    (mul_lt_mul_of_pos_left hStrict hC2Pos)

/-- The persistent alternative can be written using the intrinsic
characteristic-frequency logarithm, with no initial-energy constant
inside the logarithm. -/
theorem endpointFactor_relativeRefinedWitness_intrinsicFrequencyRateAlternative
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
              (h3TopCharacteristicFrequencyAt u (τ (k (l n))))) ^ 2 /
              ((k (l n) : ℝ) + 1))
          atTop atTop) := by
  obtain ⟨l, hNative, hRatio, hRate⟩ :=
    endpointFactor_relativeRefinedWitness_frequencyRateAlternative
      hH3 hNoExtension hClass hb hWitness
  have hΛTop : Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ (k (l n))))
      atTop atTop := by
    rcases hNative with ⟨_, _, _, _, _, hΛTop, _, _, _⟩
    exact hΛTop
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hAOne : 1 ≤
      (4 + 3 * velocityH3Energy0At u b) *
        (velocityH3Energy0At u b + 1) := by
    have hCOne : 1 ≤ 4 + 3 * velocityH3Energy0At u b := by
      linarith
    have hEOne : 1 ≤ velocityH3Energy0At u b + 1 := by
      linarith
    have hNonneg :
        0 ≤ ((4 + 3 * velocityH3Energy0At u b) - 1) *
          ((velocityH3Energy0At u b + 1) - 1) :=
      mul_nonneg (sub_nonneg.mpr hCOne) (sub_nonneg.mpr hEOne)
    nlinarith
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hRate with hVorticity | hFrequency
  · exact Or.inl hVorticity
  · exact Or.inr
      (intrinsicFrequencyRate_of_anchoredRate (fun n => k (l n))
        (fun n => h3TopCharacteristicFrequencyAt u (τ (k (l n))))
        ((4 + 3 * velocityH3Energy0At u b) *
          (velocityH3Energy0At u b + 1))
        hAOne hΛTop hFrequency)

end

end Euclidean
end Bridge
end PrimeTensor
