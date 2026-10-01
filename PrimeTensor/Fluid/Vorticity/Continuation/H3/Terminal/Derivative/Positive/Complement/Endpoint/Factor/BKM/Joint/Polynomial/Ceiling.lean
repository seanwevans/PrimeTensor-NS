import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Physical.Rate.Selection

/-!
# Joint polynomial ceiling obstruction

With a polynomial ceiling on normalized energy growth, a polynomial
ceiling on the smallest physical rate forces normalized vorticity
escape. An eventual ceiling on that vorticity rate then excludes
this relative positive-growth witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Joint original-index ceilings exclude the relative positive-growth
witness in the nonextension regime. This statement only excludes this
witness; it does not classify the other terminal regimes. -/
theorem endpointFactor_noRelativeRefinedWitness_of_jointPolynomialCeilings
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
    (B : ℝ) (rateDegree : ℕ)
    (hPhysicalCeiling : ∀ᶠ i : ℕ in atTop,
      min
          (velocityH3DissipationAt u (τ i) /
            velocityH3EnergyAt u (τ i))
          (min (h3PathTransportExcessRate u (τ i))
            ((-velocityH3TransportDerivativeAt u (τ i)) /
              velocityH3EnergyAt u (τ i))) ≤
        B * (((i : ℝ) + 1) ^ rateDegree))
    (V : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ V) :
    ¬ H3TerminalEndpointFactorRelativeRefinedWitness
        u b T p sCurl sGradient τ y k g ratio := by
  intro hWitness
  obtain ⟨l, r, hIndex, _, _, _, hVorticity⟩ :=
    endpointFactor_relativeRefinedWitness_vorticity_of_polynomialPhysicalCeiling
      hH3 hNoExtension hClass hb hg hWitness
      C growthDegree hGrowthCeiling B rateDegree hPhysicalCeiling
  have hBound := hIndex.eventually hVorticityCeiling
  have hLarge := hVorticity.eventually (eventually_gt_atTop V)
  obtain ⟨n, hnBound, hnLarge⟩ := (hBound.and hLarge).exists
  exact (not_lt_of_ge hnBound) hnLarge

end

end Euclidean
end Bridge
end PrimeTensor
