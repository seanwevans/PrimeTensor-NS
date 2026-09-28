import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMPhysicalPolynomialCeiling

/-!
# Physical branch selected by a vorticity-rate ceiling

A bound on the normalized vorticity factor along the original time
sequence excludes vorticity escape on every cofinal extracted sequence.
Under a polynomial normalized energy-growth ceiling, the remaining
branch carries superpolynomial physical rates and a dissipation corridor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The superpolynomial physical rates and their eventual common corridor. -/
def H3TerminalEndpointPhysicalDissipationCorridorData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) (m : ℕ → ℕ) : Prop :=
  H3TerminalEndpointPhysicalRateData u τ m ∧
    ∀ᶠ n : ℕ in atTop,
      velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n)) ≤
        h3PathTransportExcessRate u (τ (m n)) ∧
      h3PathTransportExcessRate u (τ (m n)) ≤
        2 * (velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n))) ∧
      2 * (velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n))) ≤
        (-velocityH3TransportDerivativeAt u (τ (m n))) /
          velocityH3EnergyAt u (τ (m n)) ∧
      (-velocityH3TransportDerivativeAt u (τ (m n))) /
          velocityH3EnergyAt u (τ (m n)) ≤
        3 * (velocityH3DissipationAt u (τ (m n)) /
          velocityH3EnergyAt u (τ (m n)))

/-- An eventual ceiling for the normalized vorticity factor selects
the physical branch on the common native and relative-rate witness. -/
theorem endpointFactor_relativeRefinedWitness_physical_of_vorticityCeiling
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
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B) :
    ∃ l r : ℕ → ℕ,
      Tendsto (fun n : ℕ => k (l (r n))) atTop atTop ∧
      (∀ n : ℕ, n ≤ r n) ∧
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient
          (fun n => τ (k (l (r n)))) (fun n => y (k (l (r n)))) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ratio (l (r n))) ∧
      H3TerminalEndpointPhysicalDissipationCorridorData u τ
        (fun n => k (l (r n))) := by
  obtain ⟨l, r, hIndex, hrIndex, hNative, hRatio, hBranches⟩ :=
    endpointFactor_relativeRefinedWitness_BKMDissipationCorridor
      hH3 hNoExtension hClass hb hg hWitness C growthDegree hGrowthCeiling
  refine ⟨l, r, hIndex, hrIndex, hNative, hRatio, ?_⟩
  rcases hBranches with hVorticity | hPhysical
  · have hBound := hIndex.eventually hVorticityCeiling
    have hLarge := hVorticity.eventually (eventually_gt_atTop B)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    exact False.elim ((not_lt_of_ge hnBound) hnLarge)
  · exact hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
