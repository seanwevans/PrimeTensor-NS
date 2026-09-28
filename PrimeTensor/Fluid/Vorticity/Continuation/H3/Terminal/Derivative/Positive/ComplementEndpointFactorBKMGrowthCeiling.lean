import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMPhysicalRatePreservation

/-!
# Original-index ceiling on endpoint energy growth

If the normalized H³ energy derivative has an eventual polynomial
upper bound on the original sequence, it cannot grow faster than
every index power on a cofinal extraction. The physical-frequency
branch must then be dissipation dominant.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Under a polynomial original-index ceiling for normalized energy
growth, the endpoint alternatives reduce to normalized vorticity
escape or a persistent dissipation-dominant physical branch. -/
theorem endpointFactor_relativeRefinedWitness_BKMGrowthCeiling
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
    (C : ℝ) (degree : ℕ)
    (hCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ degree)) :
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
        (H3TerminalEndpointPhysicalRateData u τ
            (fun n => k (l (r n))) ∧
          (∀ᶠ n : ℕ in atTop,
            h3PathTransportExcessRate u (τ (k (l (r n)))) ≤
              2 * (velocityH3DissipationAt u (τ (k (l (r n)))) /
                velocityH3EnergyAt u (τ (k (l (r n)))))))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMPhysicalRatePreservation
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | ⟨hPhysical, hSplit⟩
  · exact Or.inl hVorticity
  rcases hSplit with hDissipation | hGrowth
  · exact Or.inr ⟨hPhysical, hDissipation⟩
  have hCeilingSelected := hIndex.eventually hCeiling
  have hGrowthLarge :=
    (hGrowth degree).eventually (eventually_gt_atTop C)
  obtain ⟨n, hnLarge, hnBound⟩ :=
    (hGrowthLarge.and hCeilingSelected).exists
  have hDen : 0 < (((k (l (r n)) : ℝ) + 1) ^ degree) := by
    positivity
  have hUpper :
      (deriv (velocityH3EnergyAt u) (τ (k (l (r n)))) /
        velocityH3EnergyAt u (τ (k (l (r n))))) /
        (((k (l (r n)) : ℝ) + 1) ^ degree) ≤ C :=
    (div_le_iff₀ hDen).2 hnBound
  exact False.elim ((not_lt_of_ge hUpper) hnLarge)

end

end Euclidean
end Bridge
end PrimeTensor
