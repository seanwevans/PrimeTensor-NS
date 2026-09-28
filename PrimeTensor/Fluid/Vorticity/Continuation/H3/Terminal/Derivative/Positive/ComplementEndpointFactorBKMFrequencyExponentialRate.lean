import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMIntrinsicLogRate

/-!
# Every polynomial exponential frequency barrier on the endpoint witness

When the intrinsic frequency logarithm outruns each original-index power,
the frequency itself eventually exceeds the exponential of every fixed
multiple of every such power. This conversion stays on the same native
positive-growth witness and uses no additional extraction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A superpolynomial `1 + log Λ` rate yields every fixed exponential
polynomial lower bound for a frequency that tends to infinity. -/
theorem eventual_exponentialPolynomialFrequency_of_superpolynomialLog
    (m : ℕ → ℕ) (Λ : ℕ → ℝ)
    (hΛTop : Tendsto Λ atTop atTop)
    (hRate : ∀ degree : ℕ,
      Tendsto
        (fun n => (1 + Real.log (Λ n)) /
          (((m n : ℝ) + 1) ^ degree))
        atTop atTop)
    (C : ℝ) (degree : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (C * (((m n : ℝ) + 1) ^ degree)) < Λ n := by
  filter_upwards
      [(hRate degree).eventually (eventually_gt_atTop (C + 1)),
        hΛTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hnLarge hnΛOne
  have hScaleOne : 1 ≤ (m n : ℝ) + 1 := by
    have hnNonneg : 0 ≤ (m n : ℝ) := Nat.cast_nonneg _
    linarith
  have hPowerOne : 1 ≤ ((m n : ℝ) + 1) ^ degree :=
    one_le_pow₀ hScaleOne
  have hPowerPos : 0 < ((m n : ℝ) + 1) ^ degree :=
    lt_of_lt_of_le zero_lt_one hPowerOne
  have hLarge :
      (C + 1) * (((m n : ℝ) + 1) ^ degree) <
        1 + Real.log (Λ n) :=
    (lt_div_iff₀ hPowerPos).mp hnLarge
  have hLogLower :
      C * (((m n : ℝ) + 1) ^ degree) < Real.log (Λ n) := by
    nlinarith
  calc
    Real.exp (C * (((m n : ℝ) + 1) ^ degree)) <
        Real.exp (Real.log (Λ n)) := Real.exp_lt_exp.mpr hLogLower
    _ = Λ n := Real.exp_log (by linarith)

/-- With the polynomial energy-growth ceiling and bounded normalized
vorticity factor, the selected physical witness carries every fixed
exponential polynomial lower bound for intrinsic frequency. -/
theorem endpointFactor_relativeRefinedWitness_frequencyExponentialPolynomialRate
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
            (1 + Real.log (h3TopCharacteristicFrequencyAt u
              (τ (k (l (r n)))))) /
              (((k (l (r n)) : ℝ) + 1) ^ degree))
          atTop atTop) ∧
      (∀ M : ℝ, ∀ degree : ℕ,
        ∀ᶠ n : ℕ in atTop,
          Real.exp (M * (((k (l (r n)) : ℝ) + 1) ^ degree)) <
            h3TopCharacteristicFrequencyAt u (τ (k (l (r n))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio,
      hPhysical, hGrowthShare, hExcessShare, _, _, hIntrinsicRate⟩ :=
    endpointFactor_relativeRefinedWitness_intrinsicLogSuperpolynomial
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio,
    hPhysical, hGrowthShare, hExcessShare, hIntrinsicRate, ?_⟩
  have hNativeCopy := hNative
  obtain ⟨_, _, _, _, _, hΛTop, _, _, _⟩ := hNativeCopy
  intro M degree
  exact eventual_exponentialPolynomialFrequency_of_superpolynomialLog
    (fun n => k (l (r n)))
    (fun n => h3TopCharacteristicFrequencyAt u (τ (k (l (r n)))))
    hΛTop hIntrinsicRate M degree

end

end Euclidean
end Bridge
end PrimeTensor
