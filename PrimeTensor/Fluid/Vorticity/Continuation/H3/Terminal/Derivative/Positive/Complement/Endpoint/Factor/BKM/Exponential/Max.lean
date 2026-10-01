import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Barrier

/-!
# Exponential scale in the larger canonical endpoint factor

The canonical BKM product cannot carry an exponential square-root
index lower bound unless the larger of its two nonnegative factors
carries the corresponding squared bound. This remains a pointwise
joint alternative; the larger factor may vary with the index.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem endpointFactors_mul_le_max_sq
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    A * L ≤ (max A L) ^ 2 := by
  have hAmax : A ≤ max A L := le_max_left A L
  have hLmax : L ≤ max A L := le_max_right A L
  have hMaxNonneg : 0 ≤ max A L := hA.trans hAmax
  calc
    A * L ≤ max A L * L := mul_le_mul_of_nonneg_right hAmax hL
    _ ≤ max A L * max A L :=
      mul_le_mul_of_nonneg_left hLmax hMaxNonneg
    _ = (max A L) ^ 2 := by ring

/-- Along the refined native relative-escape witness, either the
normalized vorticity factor diverges or the maximum of the vorticity
and logarithmic energy factors carries the exponential BKM scale. -/
theorem endpointFactor_relativeRefinedWitness_canonicalBKMExponentialMax
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
          2 * Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 <
            (4 + 3 * velocityH3Energy0At u b) *
              (4422 *
                (h3BKMCanonicalSelectedLogGradientConstant
                  (Real.sqrt (velocityH3Energy0At u b)) + 1) *
                (max (1 + |g (τ (k (l n)))|)
                  (1 + Real.log
                    (velocityH3EnergyAt u (τ (k (l n)))))) ^ 2))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_canonicalBKMExponentialBarrier
      hH3 hNoExtension hClass hb hg hWitness
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
          (Real.sqrt (velocityH3Energy0At u b)) + 1) := by
    exact mul_nonneg (by norm_num) (by linarith)
  refine ⟨l, hNative, hRatio, ?_⟩
  rcases hBarrier with hVorticity | hProduct
  · exact Or.inl hVorticity
  · refine Or.inr ?_
    intro M hM
    filter_upwards [hProduct M hM] with n hn
    let A : ℝ := 1 + |g (τ (k (l n)))|
    let L : ℝ := 1 + Real.log
      (velocityH3EnergyAt u (τ (k (l n))))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hEOne : 1 ≤ velocityH3EnergyAt u (τ (k (l n))) :=
      one_le_velocityH3EnergyAt u (τ (k (l n)))
    have hL : 0 ≤ L := by
      dsimp [L]
      have hLog := Real.log_nonneg hEOne
      linarith
    have hFactors : A * L ≤ (max A L) ^ 2 :=
      endpointFactors_mul_le_max_sq A L hA hL
    have hCoeffBound :
        4422 *
          (h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt (velocityH3Energy0At u b)) + 1) * A * L ≤
        4422 *
          (h3BKMCanonicalSelectedLogGradientConstant
            (Real.sqrt (velocityH3Energy0At u b)) + 1) *
          (max A L) ^ 2 := by
      calc
        _ = (4422 *
            (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) + 1)) *
            (A * L) := by ring
        _ ≤ (4422 *
            (h3BKMCanonicalSelectedLogGradientConstant
              (Real.sqrt (velocityH3Energy0At u b)) + 1)) *
            (max A L) ^ 2 :=
          mul_le_mul_of_nonneg_left hFactors hCoeffNonneg
    exact lt_of_lt_of_le hn
      (mul_le_mul_of_nonneg_left hCoeffBound hCNonneg)

end

end Euclidean
end Bridge
end PrimeTensor
