import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Log.Energy.Frequency

/-!
# Intrinsic frequency logarithm on the exponential BKM branch

The fixed energy anchor in the amplitude corridor changes only the
coefficient of the exponential squared logarithmic frequency barrier.
The persistent native witness and all other endpoint alternatives
remain on the same indices.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem anchoredFrequencyLog_sq_le_intrinsic_sq
    (A Λ : ℝ) (hAOne : 1 ≤ A) (hΛOne : 1 ≤ Λ) :
    (1 + Real.log (A * Λ ^ 6)) ^ 2 ≤
      (A + 7) ^ 2 * (1 + Real.log Λ) ^ 2 := by
  have hAPos : 0 < A := by linarith
  have hΛPos : 0 < Λ := by linarith
  have hΛPowPos : 0 < Λ ^ 6 := pow_pos hΛPos 6
  have hExpand : Real.log (A * Λ ^ 6) =
      Real.log A + 6 * Real.log Λ := by
    rw [Real.log_mul (ne_of_gt hAPos) (ne_of_gt hΛPowPos),
      Real.log_pow]
    norm_num
  have hLogA : 0 ≤ Real.log A := Real.log_nonneg hAOne
  have hLogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛOne
  have hLogAUpper : Real.log A ≤ A :=
    Real.log_le_self (le_of_lt hAPos)
  have hLower : 0 ≤ 1 + Real.log (A * Λ ^ 6) := by
    rw [hExpand]
    linarith
  have hUpper :
      1 + Real.log (A * Λ ^ 6) ≤
        (A + 7) * (1 + Real.log Λ) := by
    rw [hExpand]
    have hExtra : 0 ≤ (A + 1) * Real.log Λ :=
      mul_nonneg (by linarith) hLogΛ
    nlinarith
  have hScaledNonneg :
      0 ≤ (A + 7) * (1 + Real.log Λ) :=
    mul_nonneg (by linarith) (by linarith)
  calc
    _ ≤ ((A + 7) * (1 + Real.log Λ)) ^ 2 :=
      (sq_le_sq₀ hLower hScaledNonneg).2 hUpper
    _ = (A + 7) ^ 2 * (1 + Real.log Λ) ^ 2 := by ring

/-- The exponential log-energy branch transfers through the corridor
to the intrinsic characteristic-frequency logarithm, with a fixed
coefficient determined by the energy anchor. -/
theorem endpointFactor_relativeRefinedWitness_BKMIntrinsicFrequency
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
          2 * Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (4422 *
                (h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt (velocityH3Energy0At u b)) + 1) *
                (1 + |g (τ (k (l (q n))))|) ^ 2)) ∨
        (∀ M : ℝ, 0 ≤ M → ∀ᶠ n : ℕ in atTop,
          2 * Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (4422 *
                (h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt (velocityH3Energy0At u b)) + 1) *
                (((4 + 3 * velocityH3Energy0At u b) *
                  (velocityH3Energy0At u b + 1) + 7) ^ 2 *
                  (1 + Real.log
                    (h3TopCharacteristicFrequencyAt u
                      (τ (k (l (q n)))))) ^ 2)))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMLogEnergyFrequency
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hOther
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inl hVorticity⟩
  rcases hOther with hExpVorticity | hExpFrequency
  · exact ⟨l, q, hqIndex, hNative, hRatio,
      Or.inr (Or.inl hExpVorticity)⟩
  have hΛTop : Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u
        (τ (k (l (q n))))) atTop atTop := by
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
  have hCNonneg : 0 ≤ 4 + 3 * velocityH3Energy0At u b := by
    linarith
  have hBNonneg :
      0 ≤ h3BKMCanonicalSelectedLogGradientConstant
        (Real.sqrt (velocityH3Energy0At u b)) :=
    h3BKMCanonicalSelectedLogGradientConstant_nonneg
      (Real.sqrt_nonneg _)
  have hCoeffNonneg :
      0 ≤ 4422 *
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) + 1) :=
    mul_nonneg (by norm_num) (by linarith)
  refine ⟨l, q, hqIndex, hNative, hRatio, Or.inr (Or.inr ?_)⟩
  intro M hM
  filter_upwards
      [hExpFrequency M hM,
        hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hΛOne
  have hSquare := anchoredFrequencyLog_sq_le_intrinsic_sq
    ((4 + 3 * velocityH3Energy0At u b) *
      (velocityH3Energy0At u b + 1))
    (h3TopCharacteristicFrequencyAt u (τ (k (l (q n)))))
    hAOne hΛOne
  have hScaled := mul_le_mul_of_nonneg_left hSquare hCoeffNonneg
  exact lt_of_lt_of_le hn
    (mul_le_mul_of_nonneg_left hScaled hCNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
