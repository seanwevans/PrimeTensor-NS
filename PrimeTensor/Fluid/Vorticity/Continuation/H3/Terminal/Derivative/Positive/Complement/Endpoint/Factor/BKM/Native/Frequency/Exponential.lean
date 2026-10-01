import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Energy.Exponential
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Intrinsic.Log.Rate

/-!
# Intrinsic frequency cost on every native endpoint witness

The amplitude corridor transfers the conditional square-root logarithmic
energy rate to the intrinsic top characteristic frequency. Both bounds
hold on the original native sequence, regardless of complement signs.
The corridor uses hypothetical nonextension, and the normalized
vorticity ceiling remains an explicit assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The intrinsic frequency logarithm eventually has a fixed positive
square-root-index lower rate on every quantitative native witness under
the normalized vorticity ceiling. -/
theorem positiveGrowth_native_intrinsicFrequency_log_sqrt_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n : ℕ in atTop,
        Real.sqrt ((n : ℝ) + 1) <
          K * (1 + Real.log (h3TopCharacteristicFrequencyAt u (τ n))) := by
  obtain ⟨D, hDPos, hEnergyRate⟩ :=
    positiveGrowth_native_canonical_logEnergy_sqrt_lower
      hH3 hClass hb hg hData hVorticityCeiling
  let A : ℝ := (4 + 3 * velocityH3Energy0At u b) *
    (velocityH3Energy0At u b + 1)
  have hE0Nonneg : 0 ≤ velocityH3Energy0At u b :=
    velocityH3Energy0At_nonneg u b
  have hAOne : 1 ≤ A := by
    dsimp [A]
    have hFirst : 1 ≤ 4 + 3 * velocityH3Energy0At u b := by linarith
    have hSecond : 1 ≤ velocityH3Energy0At u b + 1 := by linarith
    have hProduct : 0 ≤
        ((4 + 3 * velocityH3Energy0At u b) - 1) *
          ((velocityH3Energy0At u b + 1) - 1) :=
      mul_nonneg (sub_nonneg.mpr hFirst) (sub_nonneg.mpr hSecond)
    nlinarith
  have hAnchorPos : 0 < A + 7 := by linarith
  have hLogUpper := positiveGrowth_nativeWitness_logEnergy_le_frequencyLog
    hH3 hNoExtension hClass hb hData
  have hFrequencyTop :
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop := by
    rcases hData with ⟨_, _, _, _, _, hTop, _, _, _⟩
    exact hTop
  refine ⟨D * (A + 7), mul_pos hDPos hAnchorPos, ?_⟩
  filter_upwards [hEnergyRate, hLogUpper,
    hFrequencyTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with n hn hLE hnFrequency
  let Λ : ℝ := h3TopCharacteristicFrequencyAt u (τ n)
  change 1 + Real.log (velocityH3EnergyAt u (τ n)) ≤
    1 + Real.log (A * Λ ^ 6) at hLE
  have hAnchor := anchoredFrequencyLog_le_intrinsicLog
    A Λ hAOne hnFrequency
  calc
    Real.sqrt ((n : ℝ) + 1) <
        D * (1 + Real.log (velocityH3EnergyAt u (τ n))) := hn
    _ ≤ D * (1 + Real.log (A * Λ ^ 6)) :=
      mul_le_mul_of_nonneg_left hLE (le_of_lt hDPos)
    _ ≤ D * ((A + 7) * (1 + Real.log Λ)) :=
      mul_le_mul_of_nonneg_left hAnchor (le_of_lt hDPos)
    _ = (D * (A + 7)) * (1 + Real.log Λ) := by ring

/-- The intrinsic characteristic frequency itself eventually exceeds a
fixed exponential square-root-index scale on the same native witness. -/
theorem positiveGrowth_native_intrinsicFrequency_exponential_sqrt_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData : H3TerminalPositiveGrowthQuantitativeNativeData
      u b T p sCurl sGradient τ y)
    (hVorticityCeiling : ∀ᶠ n : ℕ in atTop,
      (1 + |g (τ n)|) ^ 2 / ((n : ℝ) + 1) ≤ C) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        Real.exp (c * Real.sqrt ((n : ℝ) + 1)) <
          h3TopCharacteristicFrequencyAt u (τ n) := by
  obtain ⟨K, hKPos, hSqrt⟩ :=
    positiveGrowth_native_intrinsicFrequency_log_sqrt_lower
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling
  let c : ℝ := 1 / (2 * K)
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hFrequencyTop :
      Tendsto (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
        atTop atTop := by
    rcases hData with ⟨_, _, _, _, _, hTop, _, _, _⟩
    exact hTop
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((2 * K) ^ 2)
  refine ⟨c, hcPos, ?_⟩
  filter_upwards [hSqrt, hFrequencyTop.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop N] with n hn hFrequencyPos hnN
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hIndexNonneg : 0 ≤ ((n : ℝ) + 1) := by positivity
  have hRootSq : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt hIndexNonneg
  have hRootNonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  have hLarge : 2 * K < Real.sqrt ((n : ℝ) + 1) := by
    by_contra h
    have hUpper : Real.sqrt ((n : ℝ) + 1) ≤ 2 * K :=
      le_of_not_gt h
    have hTwoKNonneg : 0 ≤ 2 * K := by positivity
    have hSquareUpper :
        (Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤ (2 * K) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hUpper)
        (add_nonneg hTwoKNonneg hRootNonneg)]
    nlinarith
  have hLog :
      c * Real.sqrt ((n : ℝ) + 1) <
        Real.log (h3TopCharacteristicFrequencyAt u (τ n)) := by
    have hHalf :
        Real.sqrt ((n : ℝ) + 1) / (2 * K) <
          Real.log (h3TopCharacteristicFrequencyAt u (τ n)) := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * K)).mpr
      nlinarith [hn, hLarge]
    simpa [c, div_eq_mul_inv, mul_comm] using hHalf
  rw [← Real.exp_log hFrequencyPos]
  exact Real.exp_lt_exp.mpr hLog

end

end Euclidean
end Bridge
end PrimeTensor
