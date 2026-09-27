import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMExponentialMax

/-!
# Persistent endpoint factor on the exponential BKM branch

The pointwise larger BKM factor can alternate. A cofinal extraction
either retains the vorticity factor whenever it is larger arbitrarily
far out, or leaves a tail on which the log-energy factor is larger.
The extraction keeps the quantitative native data and relative ratio.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem endpointFactor_cofinal_dominance
    (A L : ℕ → ℝ) :
    (∃ j : ℕ → ℕ,
      ∀ n : ℕ, n ≤ j n ∧ L (j n) ≤ A (j n)) ∨
      (∀ᶠ n : ℕ in atTop, A n ≤ L n) := by
  classical
  by_cases hCofinal :
      ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ L m ≤ A m
  · left
    choose j hj using hCofinal
    exact ⟨j, hj⟩
  · right
    push Not at hCofinal
    obtain ⟨N, hN⟩ := hCofinal
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_of_lt (hN n hn)

/-- The endpoint exponential alternative has one persistent factor
after a cofinal reindexing. Its three possible conclusions are the
earlier normalized vorticity rate, an exponential vorticity scale,
or an exponential H³ log-energy scale. -/
theorem endpointFactor_relativeRefinedWitness_canonicalBKMExponentialBranch
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
                  (velocityH3EnergyAt u (τ (k (l (q n)))))) ^ 2))) := by
  obtain ⟨l, hNative, hRatio, hBarrier⟩ :=
    endpointFactor_relativeRefinedWitness_canonicalBKMExponentialMax
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBarrier with hVorticity | hMax
  · exact ⟨l, id, (fun n => le_rfl), hNative, hRatio,
      Or.inl hVorticity⟩
  · let A : ℕ → ℝ := fun n => 1 + |g (τ (k (l n)))|
    let L : ℕ → ℝ := fun n =>
      1 + Real.log (velocityH3EnergyAt u (τ (k (l n))))
    rcases endpointFactor_cofinal_dominance A L with
        ⟨q, hq⟩ | hLarger
    · have hqTop : Tendsto q atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hq n).1
      have hNative' :
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient
              (fun n => τ (k (l (q n))))
              (fun n => y (k (l (q n)))) :=
        positiveGrowth_quantitativeNativeData_comp_cofinal hNative
          (fun n => (hq n).1)
      have hRatio' : ∀ n : ℕ,
          (n : ℝ) + 1 < ratio (l (q n)) := by
        intro n
        have hCast : (n : ℝ) ≤ (q n : ℝ) := by
          exact_mod_cast (hq n).1
        exact lt_of_le_of_lt (by linarith) (hRatio (q n))
      refine ⟨l, q, (fun n => (hq n).1), hNative', hRatio',
        Or.inr (Or.inl ?_)⟩
      intro M hM
      filter_upwards [hqTop.eventually (hMax M hM)] with n hn
      simpa only [A, L, max_eq_left (hq n).2] using hn
    · refine ⟨l, id, (fun n => le_rfl), hNative, hRatio,
        Or.inr (Or.inr ?_)⟩
      intro M hM
      filter_upwards [hMax M hM, hLarger] with n hn hnLarger
      change
        2 * Real.exp (M * Real.sqrt ((k (l n) : ℝ) + 1)) ^ 2 <
          (4 + 3 * velocityH3Energy0At u b) *
            (4422 *
              (h3BKMCanonicalSelectedLogGradientConstant
                (Real.sqrt (velocityH3Energy0At u b)) + 1) *
              (1 + Real.log
                (velocityH3EnergyAt u (τ (k (l n))))) ^ 2)
      simpa only [A, L, max_eq_right hnLarger] using hn

end

end Euclidean
end Bridge
end PrimeTensor
