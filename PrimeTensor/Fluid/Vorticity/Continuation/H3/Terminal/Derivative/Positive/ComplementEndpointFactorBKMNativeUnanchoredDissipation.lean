import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeDissipationExponential

/-!
# Removing the anchor from the native dissipation rate

A fixed positive coefficient in front of normalized dissipation can be
absorbed into a positive exponential square-root-index rate. Halving the
exponent leaves an unanchored bound on the same quantitative native
witness, without a relative-ratio or physical-corridor assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An exponential square-root-index bound absorbs any fixed positive
anchor at the cost of halving its exponent. -/
theorem indexed_exponential_sqrt_remove_anchor
    (R : ℕ → ℝ) (C c : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hRate : ∀ᶠ n : ℕ in atTop,
      Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 < C * R n) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((c / 2) * Real.sqrt ((n : ℝ) + 1)) ^ 2 < R n := by
  let B : ℝ := C + 1
  have hBPos : 0 < B := by dsimp [B]; linarith
  have hDivPos : 0 < B / c := div_pos hBPos hc
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((B / c) ^ 2)
  filter_upwards [hRate, eventually_ge_atTop N] with n hn hnN
  let s : ℝ := Real.sqrt ((n : ℝ) + 1)
  have hCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hRootSq : s ^ 2 = (n : ℝ) + 1 := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hsNonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hRootLarge : B / c < s := by
    by_contra h
    have hUpper : s ≤ B / c := le_of_not_gt h
    have hSquareUpper : s ^ 2 ≤ (B / c) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hUpper)
        (add_nonneg (le_of_lt hDivPos) hsNonneg)]
    nlinarith
  have hScale : B < c * s := by
    have hScaled := (div_lt_iff₀ hc).mp hRootLarge
    nlinarith
  have hExpLarge : C < Real.exp (c * s) := by
    have hExp := Real.add_one_le_exp (c * s)
    dsimp [B] at hScale
    linarith
  have hExpPos : 0 < Real.exp (c * s) := Real.exp_pos _
  have hAnchor : C * Real.exp (c * s) < Real.exp (c * s) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hExpLarge) hExpPos]
  have hRate' : Real.exp (c * s) ^ 2 < C * R n := hn
  have hUnanchored : Real.exp (c * s) < R n :=
    lt_of_mul_lt_mul_left (hAnchor.trans hRate') hC.le
  have hHalfSquare :
      Real.exp ((c / 2) * s) ^ 2 = Real.exp (c * s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hHalfSquare]
  exact hUnanchored

/-- The normalized full H³ dissipation itself exceeds a fixed positive
exponential square-root-index scale on the original native sequence. -/
theorem positiveGrowth_native_dissipationRatio_unanchored_exponential_sqrt_lower
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
        Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ^ 2 <
          velocityH3DissipationAt u (τ n) /
            velocityH3EnergyAt u (τ n) := by
  obtain ⟨c, hcPos, hRate⟩ :=
    positiveGrowth_native_dissipationRatio_exponential_sqrt_lower
      hH3 hNoExtension hClass hb hg hData hVorticityCeiling
  have hAnchorPos : 0 < 4 + 3 * velocityH3Energy0At u b := by
    have hEnergy0 := velocityH3Energy0At_nonneg u b
    linarith
  refine ⟨c / 2, by linarith, ?_⟩
  exact indexed_exponential_sqrt_remove_anchor
    (fun n => velocityH3DissipationAt u (τ n) /
      velocityH3EnergyAt u (τ n))
    (4 + 3 * velocityH3Energy0At u b) c
    hAnchorPos hcPos hRate

end

end Euclidean
end Bridge
end PrimeTensor
