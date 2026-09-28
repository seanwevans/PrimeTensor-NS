import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMPhysicalCeiling

/-!
# Single-exponential physical ceiling

A single exponential in the square root of the original index lies
strictly below one double-exponential endpoint scale. Consequently
an eventual single-exponential upper bound for either physical rate
selects the normalized vorticity-factor escape alternative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem singleExponential_lt_endpointScale
    (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hs : 1 ≤ s) :
    Real.exp (A * s) <
      Real.exp (Real.exp ((B * (A + 2)) * s) / B - 1) ^ 2 := by
  have hExp : 1 + (B * (A + 2)) * s ≤
      Real.exp ((B * (A + 2)) * s) := by
    linarith [Real.add_one_le_exp ((B * (A + 2)) * s)]
  have hGap : 0 < 1 + B * (2 * s - 1) := by
    have hProd : 0 < B * (2 * s - 1) :=
      mul_pos hB (by linarith)
    linarith
  have hCmp : (A * s + 1) * B <
      Real.exp ((B * (A + 2)) * s) := by
    nlinarith [hExp, hGap]
  have hDiv : A * s + 1 <
      Real.exp ((B * (A + 2)) * s) / B :=
    (lt_div_iff₀ hB).2 hCmp
  have hInner : A * s <
      Real.exp ((B * (A + 2)) * s) / B - 1 := by
    linarith
  have hAS : 0 ≤ A * s :=
    mul_nonneg hA (by linarith)
  calc
    Real.exp (A * s) <
        Real.exp
          ((Real.exp ((B * (A + 2)) * s) / B - 1) +
            (Real.exp ((B * (A + 2)) * s) / B - 1)) :=
      Real.exp_lt_exp.mpr (by linarith)
    _ = Real.exp (Real.exp ((B * (A + 2)) * s) / B - 1) ^ 2 := by
      rw [Real.exp_add, pow_two]

/-- If the smaller anchored dissipation or transport rate has an
eventual single-exponential original-index bound, the extracted
positive-growth relative-escape witness has vorticity-factor escape. -/
theorem endpointFactor_relativeRefinedWitness_vorticity_of_singleExponentialPhysicalBound
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
    (hSingle : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ j : ℕ in atTop,
      min
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ j) /
              velocityH3EnergyAt u (τ j)))
          ((4 + 3 * velocityH3Energy0At u b) *
            h3PathTransportExcessRate u (τ j)) ≤
        Real.exp (A * Real.sqrt ((j : ℝ) + 1))) :
    ∃ l q : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (q n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ q n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q n)))) (fun n => y (k (l (q n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (q n))) ∧
      Tendsto
        (fun n : ℕ =>
          (1 + |g (τ (k (l (q n))))|) ^ 2 /
            ((k (l (q n)) : ℝ) + 1))
        atTop atTop := by
  obtain ⟨A, hA, hSingle⟩ := hSingle
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
      0 ≤ h3TerminalBKMIntrinsicFrequencyCoefficient u b := by
    unfold h3TerminalBKMIntrinsicFrequencyCoefficient
    exact mul_nonneg hCNonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (by linarith))
        (sq_nonneg _))
  let B := h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hM : 0 ≤ B * (A + 2) :=
    mul_nonneg (le_of_lt hB) (by linarith)
  apply endpointFactor_relativeRefinedWitness_vorticity_of_physicalCeiling
    hH3 hNoExtension hClass hb hg hWitness
  refine ⟨B * (A + 2), hM, ?_⟩
  filter_upwards [hSingle] with j hj
  have hLower : (1 : ℝ) ≤ (j : ℝ) + 1 := by
    have hjNonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hSqrt : 1 ≤ Real.sqrt ((j : ℝ) + 1) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hLower
  exact hj.trans_lt
    (singleExponential_lt_endpointScale A B
      (Real.sqrt ((j : ℝ) + 1)) hA hB hSqrt)

end

end Euclidean
end Bridge
end PrimeTensor
