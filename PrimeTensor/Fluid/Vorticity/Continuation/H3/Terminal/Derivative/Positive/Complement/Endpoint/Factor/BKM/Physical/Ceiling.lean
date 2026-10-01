import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Original.Index

/-!
# Original-index physical ceiling on the endpoint alternative

The frequency branch forces the same explicit double-exponential
scale below both normalized dissipation and transport excess. Since
the original index is cofinal, an eventual ceiling for the smaller
of those physical rates on the original time sequence rules out that
branch and selects normalized vorticity-factor escape.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An eventual bound below one fixed double-exponential scale on
the original sequence excludes the physical-frequency branch. -/
theorem endpointFactor_relativeRefinedWitness_vorticity_of_physicalCeiling
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
    (hCeiling : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ j : ℕ in atTop,
      min
          ((4 + 3 * velocityH3Energy0At u b) *
            (velocityH3DissipationAt u (τ j) /
              velocityH3EnergyAt u (τ j)))
          ((4 + 3 * velocityH3Energy0At u b) *
            h3PathTransportExcessRate u (τ j)) <
        Real.exp
          (Real.exp (M * Real.sqrt ((j : ℝ) + 1)) /
            (h3TerminalBKMIntrinsicFrequencyCoefficient u b + 1) - 1) ^ 2) :
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
  obtain ⟨M, hM, hCeiling⟩ := hCeiling
  obtain ⟨l, q, hIndex, hqIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMOriginalIndex
      hH3 hNoExtension hClass hb hg hWitness
  refine ⟨l, q, hIndex, hqIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · exact hVorticity
  have hCeilingSelected := hIndex.eventually hCeiling
  obtain ⟨n, hn, hnPhysical⟩ :=
    (hCeilingSelected.and (hPhysical M hM)).exists
  exact False.elim ((not_lt_of_ge (le_min hnPhysical.1 hnPhysical.2)) hn)

end

end Euclidean
end Bridge
end PrimeTensor
