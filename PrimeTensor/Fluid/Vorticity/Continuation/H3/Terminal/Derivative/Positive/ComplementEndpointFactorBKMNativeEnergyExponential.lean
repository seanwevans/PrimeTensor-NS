import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeSqrtEnergy

/-!
# Exponential energy cost on a native endpoint witness

The squared logarithmic energy bound becomes a positive square-root
bound because the H³ energy tends to infinity on the quantitative native
witness. Absorbing the additive constant gives an exponential lower rate
for H³ energy under the normalized vorticity ceiling, independent of the
complement-sign branch. The ceiling remains a hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Convert an eventual squared logarithmic rate into a square-root rate
when the unsquared factor is eventually positive. -/
theorem indexed_square_lower_to_sqrt
    (L : ℕ → ℝ)
    (hLTop : Tendsto L atTop atTop)
    (hSquare : ∃ D : ℝ, 0 < D ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 < D * (L n) ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n : ℕ in atTop,
        Real.sqrt ((n : ℝ) + 1) < K * L n := by
  obtain ⟨D, hDPos, hSquare⟩ := hSquare
  let K : ℝ := D + 1
  have hKPos : 0 < K := by dsimp [K]; linarith
  have hCoeff : D < K ^ 2 := by
    dsimp [K]
    nlinarith [sq_nonneg D]
  refine ⟨K, hKPos, ?_⟩
  filter_upwards [hSquare, hLTop.eventually (eventually_gt_atTop 0)]
    with n hn hLPos
  have hSNonneg : 0 ≤ ((n : ℝ) + 1) := by positivity
  have hRootSq : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt hSNonneg
  have hFactorSq : D * (L n) ^ 2 < K ^ 2 * (L n) ^ 2 :=
    mul_lt_mul_of_pos_right hCoeff (by positivity)
  have hSquares :
      (Real.sqrt ((n : ℝ) + 1)) ^ 2 < (K * L n) ^ 2 := by
    calc
      (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 := hRootSq
      _ < D * (L n) ^ 2 := hn
      _ < K ^ 2 * (L n) ^ 2 := hFactorSq
      _ = (K * L n) ^ 2 := by ring
  have hRootNonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  have hProductPos : 0 < K * L n := mul_pos hKPos hLPos
  by_contra h
  have hReverse : K * L n ≤ Real.sqrt ((n : ℝ) + 1) :=
    le_of_not_gt h
  have hSquareReverse :
      (K * L n) ^ 2 ≤ (Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hReverse)
      (add_nonneg (le_of_lt hProductPos) hRootNonneg)]
  exact (not_le_of_gt hSquares) hSquareReverse

/-- On the unchanged native sequence, the canonical logarithmic H³
energy factor eventually exceeds a fixed positive multiple of the
square root of the original witness index. -/
theorem positiveGrowth_native_canonical_logEnergy_sqrt_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
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
          K * (1 + Real.log (velocityH3EnergyAt u (τ n))) := by
  exact indexed_square_lower_to_sqrt _
    (positiveGrowth_relativeWitness_logEnergyFactor_atTop
      hData tendsto_id)
    (positiveGrowth_native_canonical_logEnergy_square_lower
      hH3 hClass hb hg hData hVorticityCeiling)

/-- Under the same normalized vorticity ceiling, the native H³ energy
eventually exceeds an exponential in the square root of the witness
index. This is a necessary conditional rate in every complement branch. -/
theorem positiveGrowth_native_canonical_energy_exponential_sqrt_lower
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ} {y : ℕ → Point3}
    {g : ℝ → ℝ} {C : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
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
          velocityH3EnergyAt u (τ n) := by
  obtain ⟨K, hKPos, hSqrt⟩ :=
    positiveGrowth_native_canonical_logEnergy_sqrt_lower
      hH3 hClass hb hg hData hVorticityCeiling
  let c : ℝ := 1 / (2 * K)
  have hcPos : 0 < c := by dsimp [c]; positivity
  have hEnergyTop :
      Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ n)) atTop atTop := by
    rcases hData with ⟨_, _, hEnergy, _, _, _, _, _, _⟩
    exact hEnergy
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((2 * K) ^ 2)
  refine ⟨c, hcPos, ?_⟩
  filter_upwards [hSqrt, hEnergyTop.eventually (eventually_gt_atTop 0),
    eventually_ge_atTop N] with n hn hEnergyPos hnN
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
        Real.log (velocityH3EnergyAt u (τ n)) := by
    have hHalf :
        Real.sqrt ((n : ℝ) + 1) / (2 * K) <
          Real.log (velocityH3EnergyAt u (τ n)) := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * K)).mpr
      nlinarith [hn, hLarge]
    simpa [c, div_eq_mul_inv, mul_comm] using hHalf
  rw [← Real.exp_log hEnergyPos]
  exact Real.exp_lt_exp.mpr hLog

end

end Euclidean
end Bridge
end PrimeTensor
