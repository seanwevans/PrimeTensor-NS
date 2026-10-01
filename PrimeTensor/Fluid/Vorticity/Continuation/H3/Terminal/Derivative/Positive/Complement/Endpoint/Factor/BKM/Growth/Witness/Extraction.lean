import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Relative.Physical.Split

/-!
# Native witness on the endpoint energy-growth branch

The cofinal energy-growth extraction can be absorbed into the
relative-escape witness. Its native data, quantitative index bound,
original-index cofinality, and relative-ratio inequality all persist.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The endpoint physical split can be stated on one native witness:
vorticity-factor escape, eventual dissipation dominance, or
superpolynomial logarithmic energy growth at every index degree. -/
theorem endpointFactor_relativeRefinedWitness_BKMGrowthWitnessExtraction
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
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      (Tendsto
          (fun n : ℕ =>
            (1 + |g (τ (k (l (r n))))|) ^ 2 /
              ((k (l (r n)) : ℝ) + 1))
          atTop atTop ∨
        (∀ᶠ n : ℕ in atTop,
          h3PathTransportExcessRate u (τ (k (l (r n)))) ≤
            2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
              velocityH3EnergyAt u (τ (k (l (r n)))))) ∨
        (∀ degree : ℕ,
          Tendsto
            (fun n : ℕ =>
              (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n))))) /
                (((k (l (r n)) : ℝ) + 1) ^ degree))
            atTop atTop)) := by
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMRelativePhysicalSplit
      hH3 hNoExtension hClass hb hg hWitness
  rcases hBranches with hVorticity | hPhysical
  · exact ⟨l, q, hIndex, hqIndex, hNative, hRatio,
      Or.inl hVorticity⟩
  rcases hPhysical with hDissipation | ⟨j, hj, hGrowth⟩
  · exact ⟨l, q, hIndex, hqIndex, hNative, hRatio,
      Or.inr (Or.inl hDissipation)⟩
  have hjTop : Tendsto j atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hj n)
  have hNative' :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (q (j n)))))
          (fun n => y (k (l (q (j n))))) :=
    positiveGrowth_quantitativeNativeData_comp_cofinal hNative hj
  have hRatio' : ∀ n : ℕ,
      (n : ℝ) + 1 < ratio (l (q (j n))) := by
    intro n
    have hCast : (n : ℝ) ≤ (j n : ℝ) := by
      exact_mod_cast (hj n)
    exact lt_of_le_of_lt (by linarith) (hRatio (j n))
  exact ⟨l, (fun n => q (j n)), hIndex.comp hjTop,
    (fun n => (hj n).trans (hqIndex (j n))),
    hNative', hRatio', Or.inr (Or.inr hGrowth)⟩

end

end Euclidean
end Bridge
end PrimeTensor
