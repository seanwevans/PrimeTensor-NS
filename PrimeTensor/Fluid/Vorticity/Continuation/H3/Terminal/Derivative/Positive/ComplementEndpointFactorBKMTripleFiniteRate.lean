import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMFiniteRateDichotomy

/-!
# Finite relative rates on a triple native endpoint cascade

The triple native cascade supplies one cancellation-compatible quantitative
sequence and its positive relative-gap orientation. Under hypothetical
nonextension, the endpoint growth, vorticity, and physical ceilings on that
selected sequence force a finite relative-rate dichotomy there.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Select the relative-gap witness from a triple native cascade. Whenever
the three endpoint ceilings hold on this fixed witness, its only finite
relative-rate outcomes are matching and positive finite separation. -/
theorem positiveGrowth_tripleNative_endpoint_finiteRateDichotomy_of_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient sComplement : H3TerminalOrientation}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hTriple :
      H3TerminalPositiveGrowthTripleNativeCascade
        u b T p sCurl sGradient sComplement) :
    ∃ τ : ℕ → ℝ,
      ∃ y : ℕ → Point3,
        H3TerminalPositiveGrowthQuantitativeNativeData
          u b T p sCurl sGradient τ y ∧
        H3TerminalComplementCancellationRegime p sCurl sGradient ∧
        H3TerminalPositiveGrowthRelativeGapAt
          u p sGradient sComplement τ y ∧
        ∀ (g : ℝ → ℝ),
          (∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) →
          ∀ (C : ℝ) (growthDegree : ℕ),
            (∀ᶠ i : ℕ in atTop,
              deriv (velocityH3EnergyAt u) (τ i) /
                  velocityH3EnergyAt u (τ i) ≤
                C * (((i : ℝ) + 1) ^ growthDegree)) →
            ∀ B : ℝ,
              (∀ᶠ i : ℕ in atTop,
                (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B) →
              H3TerminalEndpointExponentialPhysicalCeilingData u τ →
              H3TerminalEndpointFiniteRateDichotomyAt
                u b T p sCurl sGradient sComplement τ y := by
  obtain ⟨τ, y, hData, hCancellation, hRelative⟩ :=
    positiveGrowth_relativeGap_of_tripleNativeCascade hTriple
  refine ⟨τ, y, hData, hCancellation, hRelative, ?_⟩
  intro g hg C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  exact positiveGrowth_endpoint_finiteRateDichotomy_of_exponentialCeiling
    hH3 hNoExtension hClass hb hg hData hCancellation hRelative
    C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
