import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMUnanchoredNormalizedRates

/-!
# Exponential normalized physical ceiling obstruction

The common physical witness forces normalized full H³ dissipation and
one-copy transport excess above every fixed exponential polynomial square.
An eventual original-index upper ceiling on either normalized rate pulls
back along the cofinal selected indices and contradicts that strict bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- An exponential polynomial ceiling on normalized dissipation or
one-copy transport excess excludes the relative refined endpoint witness. -/
theorem endpointFactor_no_relativeRefinedWitness_of_exponentialNormalizedCeiling
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
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (Ad Aq : ℝ) (dissipationDegree excessDegree : ℕ)
    (hNormalizedCeiling :
      (∀ᶠ i : ℕ in atTop,
        velocityH3DissipationAt u (τ i) / velocityH3EnergyAt u (τ i) ≤
          Real.exp (Ad * (((i : ℝ) + 1) ^ dissipationDegree)) ^ 2) ∨
      (∀ᶠ i : ℕ in atTop,
        h3PathTransportExcessRate u (τ i) ≤
          Real.exp (Aq * (((i : ℝ) + 1) ^ excessDegree)) ^ 2)) :
    ¬ H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio := by
  intro hWitness
  obtain ⟨l, r, hIndex, _, _, _, _, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_unanchoredNormalizedRates
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  rcases hNormalizedCeiling with hDCeiling | hQCeiling
  · have hBound := hIndex.eventually hDCeiling
    have hLarge := (hRates Ad dissipationDegree).mono (fun n hn => hn.1)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    exact (not_lt_of_ge hnBound) hnLarge
  · have hBound := hIndex.eventually hQCeiling
    have hLarge := (hRates Aq excessDegree).mono (fun n hn => hn.2)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    exact (not_lt_of_ge hnBound) hnLarge

end

end Euclidean
end Bridge
end PrimeTensor
