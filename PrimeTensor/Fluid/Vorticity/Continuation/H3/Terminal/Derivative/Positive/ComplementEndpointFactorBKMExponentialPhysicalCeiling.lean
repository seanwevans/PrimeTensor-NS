import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMUnanchoredExponentialRates

/-!
# Exponential physical ceiling obstruction for the endpoint witness

On a cofinal original-index subsequence, raw growth plus dissipation and
the raw adverse-transport balance gap each exceed every fixed exponential
polynomial square. An eventual upper ceiling of that form for either
physical quantity therefore excludes the relative refined witness under
the growth and vorticity hypotheses selecting the physical branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A fixed original-index exponential ceiling on either raw physical
rate is incompatible with the common endpoint witness. -/
theorem endpointFactor_no_relativeRefinedWitness_of_exponentialPhysicalCeiling
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
    (Araw Agap : ℝ) (rawDegree gapDegree : ℕ)
    (hPhysicalCeiling :
      (∀ᶠ i : ℕ in atTop,
        deriv (velocityH3EnergyAt u) (τ i) +
            velocityH3DissipationAt u (τ i) ≤
          Real.exp (Araw * (((i : ℝ) + 1) ^ rawDegree)) ^ 2) ∨
      (∀ᶠ i : ℕ in atTop,
        (-velocityH3TransportDerivativeAt u (τ i)) -
            deriv (velocityH3EnergyAt u) (τ i) ≤
          Real.exp (Agap * (((i : ℝ) + 1) ^ gapDegree)) ^ 2)) :
    ¬ H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio := by
  intro hWitness
  obtain ⟨l, r, hIndex, _, _, _, _, hRates⟩ :=
    endpointFactor_relativeRefinedWitness_unanchoredExponentialRates
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
  rcases hPhysicalCeiling with hRawCeiling | hGapCeiling
  · have hBound := hIndex.eventually hRawCeiling
    have hLarge := (hRates Araw rawDegree).mono (fun n hn => hn.1)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    exact (not_lt_of_ge hnBound) hnLarge
  · have hBound := hIndex.eventually hGapCeiling
    have hLarge := (hRates Agap gapDegree).mono (fun n hn => hn.2)
    obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
    exact (not_lt_of_ge hnBound) hnLarge

end

end Euclidean
end Bridge
end PrimeTensor
