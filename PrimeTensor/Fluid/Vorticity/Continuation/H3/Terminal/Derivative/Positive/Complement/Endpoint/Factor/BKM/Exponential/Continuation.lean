import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Normalized.Ceiling

/-!
# Conditional continuation from exponential endpoint physical ceilings

The preceding raw and normalized ceiling obstructions rule out the refined
endpoint witness when smooth continuation fails. Equivalently, if that
witness and one of the stated physical ceilings are present, the path has
a smooth continuation through the endpoint. The hypotheses retain the
polynomial normalized growth ceiling and bounded vorticity factor.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- On a refined endpoint witness, an exponential ceiling on either raw
physical rate or either normalized physical rate forces smooth extension. -/
theorem endpointFactor_relativeRefinedWitness_extension_of_exponentialPhysicalCeiling
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
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (Araw Agap Ad Aq : ℝ)
    (rawDegree gapDegree dissipationDegree excessDegree : ℕ)
    (hCeiling :
      ((∀ᶠ i : ℕ in atTop,
          deriv (velocityH3EnergyAt u) (τ i) +
              velocityH3DissipationAt u (τ i) ≤
            Real.exp (Araw * (((i : ℝ) + 1) ^ rawDegree)) ^ 2) ∨
        (∀ᶠ i : ℕ in atTop,
          (-velocityH3TransportDerivativeAt u (τ i)) -
              deriv (velocityH3EnergyAt u) (τ i) ≤
            Real.exp (Agap * (((i : ℝ) + 1) ^ gapDegree)) ^ 2)) ∨
      ((∀ᶠ i : ℕ in atTop,
          velocityH3DissipationAt u (τ i) / velocityH3EnergyAt u (τ i) ≤
            Real.exp (Ad * (((i : ℝ) + 1) ^ dissipationDegree)) ^ 2) ∨
        (∀ᶠ i : ℕ in atTop,
          h3PathTransportExcessRate u (τ i) ≤
            Real.exp (Aq * (((i : ℝ) + 1) ^ excessDegree)) ^ 2))) :
    ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T := by
  by_contra hNoExtension
  rcases hCeiling with hRaw | hNormalized
  · exact (endpointFactor_no_relativeRefinedWitness_of_exponentialPhysicalCeiling
      hH3 hNoExtension hClass hb hg
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Araw Agap rawDegree gapDegree hRaw) hWitness
  · exact (endpointFactor_no_relativeRefinedWitness_of_exponentialNormalizedCeiling
      hH3 hNoExtension hClass hb hg
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Ad Aq dissipationDegree excessDegree hNormalized) hWitness

end

end Euclidean
end Bridge
end PrimeTensor
