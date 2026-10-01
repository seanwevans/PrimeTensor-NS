import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Double.Dissipation

/-!
# Original extraction index on the endpoint witness

Selected times below the terminal time converge to that terminal
time. A fixed finite set of original indices cannot support those
times indefinitely. Consequently the original selected index is
cofinal on the quantitative native witness and on both BKM branches.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem terminalTimeIndex_cofinal
    (τ : ℕ → ℝ) (m : ℕ → ℕ) (T : ℝ)
    (hBelow : ∀ n : ℕ, τ (m n) < T)
    (hTime : Tendsto (fun n : ℕ => τ (m n)) atTop (𝓝 T)) :
    Tendsto m atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro K
  have hAvoid :
      ∀ i ∈ Finset.range K, ∀ᶠ n : ℕ in atTop, m n ≠ i := by
    intro i hi
    by_cases hiT : τ i < T
    · have hLate : ∀ᶠ n : ℕ in atTop, τ i < τ (m n) :=
        (tendsto_order.1 hTime).1 (τ i) hiT
      filter_upwards [hLate] with n hn hEq
      rw [hEq] at hn
      exact (lt_irrefl _) hn
    · exact Eventually.of_forall (fun n hEq => by
        have hnBelow := hBelow n
        rw [hEq] at hnBelow
        exact (not_lt_of_ge (le_of_not_gt hiT)) hnBelow)
  have hAll :
      ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range K, m n ≠ i :=
    (Finset.eventually_all (Finset.range K)).2 hAvoid
  filter_upwards [hAll] with n hn
  by_contra hNot
  have hm : m n < K := Nat.lt_of_not_ge hNot
  exact (hn (m n) (Finset.mem_range.mpr hm)) rfl

/-- The original index of any quantitative native positive-growth
subsequence must tend to infinity. -/
theorem positiveGrowth_nativeWitness_originalIndex_atTop
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {m : ℕ → ℕ}
    (hNative :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (m n)) (fun n => y (m n))) :
    Tendsto m atTop atTop := by
  obtain ⟨hAt, hTime, _, _, _, _, _, _, _⟩ := hNative
  exact terminalTimeIndex_cofinal τ m T
    (fun n => (hAt n).1.2) hTime

/-- The two persistent endpoint growth mechanisms retain a cofinal
original selected index. In the frequency branch, the physical
dissipation and transport bounds hold on that same index. -/
theorem endpointFactor_relativeRefinedWitness_BKMOriginalIndex
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
      Tendsto (fun n : ℕ => k (l (q n))) atTop atTop ∧
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
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              (velocityH3DissipationAt u (τ (k (l (q n)))) /
                velocityH3EnergyAt u (τ (k (l (q n))))) ∧
          Real.exp
            (Real.exp (M * Real.sqrt ((k (l (q n)) : ℝ) + 1)) /
              (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2 ≤
            (4 + 3 * velocityH3Energy0At u b) *
              h3PathTransportExcessRate u (τ (k (l (q n)))))) := by
  obtain ⟨l, q, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMDoubleDissipation
      hH3 hNoExtension hClass hb hg hWitness
  exact ⟨l, q,
    positiveGrowth_nativeWitness_originalIndex_atTop hNative,
    hqIndex, hNative, hRatio, hBranches⟩

end

end Euclidean
end Bridge
end PrimeTensor
