import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Adverse.Transport.Rate

/-!
# Energy growth versus dissipation in the endpoint physical branch

At positive-growth times the one-copy excess is the sum of the
normalized energy derivative and normalized dissipation. Either
dissipation carries at least half of that excess eventually, or a
cofinal subsequence carries superpolynomial logarithmic energy growth.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem half_excess_growth_atTop
    (j : ℕ → ℕ) (Q D P : ℕ → ℝ)
    (hP : ∀ n, 0 < P n)
    (hQ : Tendsto (fun n => Q (j n) / P (j n)) atTop atTop)
    (hHalf : ∀ n, Q (j n) ≤ 2 * D (j n)) :
    Tendsto (fun n => D (j n) / P (j n)) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C
  filter_upwards [hQ.eventually (eventually_ge_atTop (2 * C))] with n hn
  have hMul : (2 * C) * P (j n) ≤ Q (j n) :=
    (le_div_iff₀ (hP (j n))).1 hn
  have hGrowth : C * P (j n) ≤ D (j n) := by
    nlinarith [hMul, hHalf n]
  exact (le_div_iff₀ (hP (j n))).2 hGrowth

/-- A cofinal half-excess split for an exact sum of two rates. -/
theorem endpointPhysical_halfExcess_split
    (Q D R : ℕ → ℝ) (P : ℕ → ℕ → ℝ)
    (hEq : ∀ n, Q n = D n + R n)
    (hP : ∀ degree n, 0 < P degree n)
    (hQ : ∀ degree : ℕ,
      Tendsto (fun n => Q n / P degree n) atTop atTop) :
    (∀ᶠ n : ℕ in atTop, Q n ≤ 2 * R n) ∨
      (∃ j : ℕ → ℕ,
        (∀ n : ℕ, n ≤ j n) ∧
        (∀ degree : ℕ,
          Tendsto (fun n => D (j n) / P degree (j n)) atTop atTop)) := by
  classical
  by_cases hCofinal :
      ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ 2 * R m < Q m
  · right
    choose j hj using hCofinal
    have hjTop : Tendsto j atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro N
      filter_upwards [eventually_ge_atTop N] with n hn
      exact hn.trans (hj n).1
    refine ⟨j, (fun n => (hj n).1), ?_⟩
    intro degree
    have hCompare : ∀ n, Q (j n) ≤ 2 * D (j n) := by
      intro n
      have hEqAt := hEq (j n)
      have hDominance := (hj n).2
      linarith
    exact half_excess_growth_atTop j Q D (P degree)
      (hP degree) ((hQ degree).comp hjTop) hCompare
  · left
    push Not at hCofinal
    obtain ⟨N, hN⟩ := hCofinal
    filter_upwards [eventually_ge_atTop N] with n hn
    have hBound := hN n hn
    linarith

/-- On the persistent physical branch, either normalized dissipation
carries at least half of the one-copy excess eventually, or an
additional cofinal extraction makes logarithmic energy growth
superpolynomial at every original-index degree. -/
theorem endpointFactor_relativeRefinedWitness_BKMRelativePhysicalSplit
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
        ((∀ᶠ n : ℕ in atTop,
            h3PathTransportExcessRate u (τ (k (l (q n)))) ≤
              2 * (velocityH3DissipationAt u (τ (k (l (q n)))) /
                velocityH3EnergyAt u (τ (k (l (q n)))))) ∨
          (∃ j : ℕ → ℕ,
            (∀ n : ℕ, n ≤ j n) ∧
            (∀ degree : ℕ,
              Tendsto
                (fun n : ℕ =>
                  (deriv (velocityH3EnergyAt u) (τ (k (l (q (j n))))) /
                    velocityH3EnergyAt u (τ (k (l (q (j n)))))) /
                    (((k (l (q (j n))) : ℝ) + 1) ^ degree))
                atTop atTop)))) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMAdverseTransportRate
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact Or.inl hVorticity
  right
  obtain ⟨hAt, _, _, _, _, _, _, _, _⟩ := hNative
  have hBalance : ∀ n : ℕ,
      h3PathTransportExcessRate u (τ (k (l (q n)))) =
        deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) +
        velocityH3DissipationAt u (τ (k (l (q n)))) /
          velocityH3EnergyAt u (τ (k (l (q n)))) := by
    intro n
    have ht : τ (k (l (q n))) ∈ Set.Ioo a T :=
      ⟨lt_trans hb.1 (hAt n).1.1, (hAt n).1.2⟩
    have hDerivative :
        0 ≤ deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) :=
      (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n).trans
        (le_of_lt (hAt n).2.2.1)
    exact h3PathTransportExcessRate_eq_deriv_div_energy_add_dissipation_div_energy_of_nonnegative_deriv
      hH3 hClass ht hDerivative
  exact endpointPhysical_halfExcess_split
    (fun n => h3PathTransportExcessRate u (τ (k (l (q n)))))
    (fun n =>
      deriv (velocityH3EnergyAt u) (τ (k (l (q n)))) /
        velocityH3EnergyAt u (τ (k (l (q n)))))
    (fun n =>
      velocityH3DissipationAt u (τ (k (l (q n)))) /
        velocityH3EnergyAt u (τ (k (l (q n)))))
    (fun degree n => ((k (l (q n)) : ℝ) + 1) ^ degree)
    hBalance (fun degree n => by positivity)
    (fun degree => (hPhysical degree).2.1)

end

end Euclidean
end Bridge
end PrimeTensor
