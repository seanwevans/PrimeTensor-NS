import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMFrequencyLogRate

/-!
# Intrinsic logarithmic frequency rate on the physical endpoint witness

The fixed energy anchor in the characteristic-frequency amplitude corridor
changes the logarithmic frequency factor by at most a fixed multiplier.
The superpolynomial anchored rate therefore forces the intrinsic factor
`1 + log Λ₃` above every original-index polynomial on the same witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A fixed positive multiplier does not affect superpolynomial
divergence after division by each power of a positive scale. -/
theorem superpolynomial_rate_of_eventual_fixed_multiple
    (F G scale : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hScale : ∀ n, 0 < scale n)
    (hF : ∀ degree : ℕ,
      Tendsto (fun n => F n / scale n ^ degree) atTop atTop)
    (hBound : ∀ᶠ n : ℕ in atTop, F n ≤ C * G n) :
    ∀ degree : ℕ,
      Tendsto (fun n => G n / scale n ^ degree) atTop atTop := by
  intro degree
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards
      [(hF degree).eventually (eventually_ge_atTop (C * max M 0)), hBound]
    with n hnLarge hnBound
  have hp : 0 < scale n ^ degree := pow_pos (hScale n) _
  have hLower : C * max M 0 * scale n ^ degree ≤ F n :=
    (le_div_iff₀ hp).mp hnLarge
  have hScaled : C * (max M 0 * scale n ^ degree) ≤ C * G n := by
    calc
      _ = C * max M 0 * scale n ^ degree := by ring
      _ ≤ F n := hLower
      _ ≤ C * G n := hnBound
  have hGLower : max M 0 * scale n ^ degree ≤ G n := by
    by_contra hNot
    have hStrict : G n < max M 0 * scale n ^ degree := lt_of_not_ge hNot
    have hStrictScaled := mul_lt_mul_of_pos_left hStrict hC
    exact (not_lt_of_ge hScaled) hStrictScaled
  have hDiv : max M 0 ≤ G n / scale n ^ degree :=
    (le_div_iff₀ hp).2 hGLower
  exact (le_max_left M 0).trans hDiv

/-- For a fixed anchor at least one and a frequency at least one,
the anchored logarithm is bounded by a fixed multiple of the
intrinsic frequency logarithm. -/
theorem anchoredFrequencyLog_le_intrinsicLog
    (A Λ : ℝ) (hAOne : 1 ≤ A) (hΛOne : 1 ≤ Λ) :
    1 + Real.log (A * Λ ^ 6) ≤
      (A + 7) * (1 + Real.log Λ) := by
  have hAPos : 0 < A := by linarith
  have hΛPos : 0 < Λ := by linarith
  have hΛPowPos : 0 < Λ ^ 6 := pow_pos hΛPos 6
  have hExpand : Real.log (A * Λ ^ 6) =
      Real.log A + 6 * Real.log Λ := by
    rw [Real.log_mul (ne_of_gt hAPos) (ne_of_gt hΛPowPos),
      Real.log_pow]
    norm_num
  have hLogAUpper : Real.log A ≤ A :=
    Real.log_le_self (le_of_lt hAPos)
  have hLogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛOne
  have hExtra : 0 ≤ (A + 1) * Real.log Λ :=
    mul_nonneg (by linarith) hLogΛ
  rw [hExpand]
  nlinarith

/-- Under the same conditional physical-branch ceilings, the intrinsic
characteristic-frequency logarithm outruns every fixed original-index
power. All previously selected native and physical data persist. -/
theorem endpointFactor_relativeRefinedWitness_intrinsicLogSuperpolynomial
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
        u b T p sCurl sGradient τ y k g ratio)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      H3TerminalEndpointPhysicalDissipationCorridorData u τ
        (fun n => k (l (r n))) ∧
      Tendsto
        (fun n : ℕ =>
          (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
            velocityH3EnergyAt u (τ (k (l (r n))))) /
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 (0 : ℝ)) ∧
      Tendsto
        (fun n : ℕ =>
          h3PathTransportExcessRate u (τ (k (l (r n)))) /
          ((-velocityH3TransportDerivativeAt u (τ (k (l (r n))))) /
            velocityH3EnergyAt u (τ (k (l (r n))))))
        atTop (𝓝 ((1 : ℝ) / 2)) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (velocityH3EnergyAt u (τ (k (l (r n)))))) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log
              ((4 + 3 * velocityH3Energy0At u b) *
                (velocityH3Energy0At u b + 1) *
                h3TopCharacteristicFrequencyAt u
                  (τ (k (l (r n)))) ^ 6)) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) ∧
      (∀ degree : ℕ,
        Tendsto
          (fun n : ℕ =>
            (1 + Real.log (h3TopCharacteristicFrequencyAt u
              (τ (k (l (r n)))))) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, hGrowthShare, hExcessShare, hLogRate, hAnchoredRate⟩ :=
    endpointFactor_relativeRefinedWitness_anchoredFrequencyLogSuperpolynomial
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio,
    hPhysical, hGrowthShare, hExcessShare, hLogRate, hAnchoredRate, ?_⟩
  let A : ℝ := (4 + 3 * velocityH3Energy0At u b) *
    (velocityH3Energy0At u b + 1)
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hAOne : 1 ≤ A := by
    dsimp [A]
    have hCOne : 1 ≤ 4 + 3 * velocityH3Energy0At u b := by linarith
    have hEOne : 1 ≤ velocityH3Energy0At u b + 1 := by linarith
    have hProduct : 0 ≤
        ((4 + 3 * velocityH3Energy0At u b) - 1) *
          ((velocityH3Energy0At u b + 1) - 1) :=
      mul_nonneg (sub_nonneg.mpr hCOne) (sub_nonneg.mpr hEOne)
    nlinarith
  have hCPos : 0 < A + 7 := by linarith
  have hNativeCopy := hNative
  obtain ⟨_, _, _, _, _, hΛTop, _, _, _⟩ := hNativeCopy
  have hUpper : ∀ᶠ n : ℕ in atTop,
      1 + Real.log (A *
        h3TopCharacteristicFrequencyAt u (τ (k (l (r n)))) ^ 6) ≤
      (A + 7) *
        (1 + Real.log (h3TopCharacteristicFrequencyAt u
          (τ (k (l (r n)))))) := by
    filter_upwards [hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hnΛ
    exact anchoredFrequencyLog_le_intrinsicLog A _ hAOne hnΛ
  exact superpolynomial_rate_of_eventual_fixed_multiple
    (fun n => 1 + Real.log (A *
      h3TopCharacteristicFrequencyAt u (τ (k (l (r n)))) ^ 6))
    (fun n => 1 + Real.log (h3TopCharacteristicFrequencyAt u
      (τ (k (l (r n))))))
    (fun n => (k (l (r n)) : ℝ) + 1)
    (A + 7) hCPos (fun n => by positivity) hAnchoredRate hUpper

end

end Euclidean
end Bridge
end PrimeTensor
