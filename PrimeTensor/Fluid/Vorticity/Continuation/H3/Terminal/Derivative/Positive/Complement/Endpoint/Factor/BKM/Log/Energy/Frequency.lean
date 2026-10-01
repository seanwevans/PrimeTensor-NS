import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Branch
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.Frequency.Log

/-!
# Frequency consequence of the exponential log-energy branch

The existing amplitude corridor bounds the logarithmic H³ energy
factor above by an anchored logarithm of the sixth power of the
characteristic frequency. On the persistent exponential log-energy
branch, its squared lower barrier transfers to that frequency log.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The persistent endpoint branches retain the native and ratio
witness. In the log-energy branch, the exponential squared lower bound
also holds for the anchored characteristic-frequency logarithm. -/
theorem endpointFactor_relativeRefinedWitness_BKMLogEnergyFrequency
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
                (1 + Real.log
                  ((4 + 3 * velocityH3Energy0At u b) *
                    (velocityH3Energy0At u b + 1) *
                    h3TopCharacteristicFrequencyAt u
                      (τ (k (l (q n)))) ^ 6)) ^ 2))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_canonicalBKMExponentialBranch
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hOther
  · exact ⟨l, q, hqIndex, hNative, hRatio, Or.inl hVorticity⟩
  rcases hOther with hExpVorticity | hExpLogEnergy
  · exact ⟨l, q, hqIndex, hNative, hRatio,
      Or.inr (Or.inl hExpVorticity)⟩
  have hUpper :=
    positiveGrowth_nativeWitness_logEnergy_le_frequencyLog
      hH3 hNoExtension hClass hb hNative
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
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
  filter_upwards [hExpLogEnergy M hM, hUpper] with n hn hLE
  have hEOne :
      1 ≤ velocityH3EnergyAt u (τ (k (l (q n)))) :=
    one_le_velocityH3EnergyAt u (τ (k (l (q n))))
  have hLNonneg :
      0 ≤ 1 + Real.log
        (velocityH3EnergyAt u (τ (k (l (q n))))) := by
    have hLog := Real.log_nonneg hEOne
    linarith
  have hSquare :
      (1 + Real.log
        (velocityH3EnergyAt u (τ (k (l (q n)))))) ^ 2 ≤
      (1 + Real.log
        ((4 + 3 * velocityH3Energy0At u b) *
          (velocityH3Energy0At u b + 1) *
          h3TopCharacteristicFrequencyAt u
            (τ (k (l (q n)))) ^ 6)) ^ 2 :=
    (sq_le_sq₀ hLNonneg (hLNonneg.trans hLE)).2 hLE
  have hScaled :
      4422 *
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) + 1) *
        (1 + Real.log
          (velocityH3EnergyAt u (τ (k (l (q n)))))) ^ 2 ≤
      4422 *
        (h3BKMCanonicalSelectedLogGradientConstant
          (Real.sqrt (velocityH3Energy0At u b)) + 1) *
        (1 + Real.log
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3Energy0At u b + 1) *
            h3TopCharacteristicFrequencyAt u
              (τ (k (l (q n)))) ^ 6)) ^ 2 :=
    mul_le_mul_of_nonneg_left hSquare hCoeffNonneg
  exact lt_of_lt_of_le hn
    (mul_le_mul_of_nonneg_left hScaled hCNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
