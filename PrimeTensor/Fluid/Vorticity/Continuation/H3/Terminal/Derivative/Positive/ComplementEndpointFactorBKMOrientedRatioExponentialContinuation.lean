import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMCurlRatioExponentialContinuation

/-!
# Oriented ratio escape with exponential physical continuation

The two oriented relative-ratio branches share the same quantitative native
cascade and physical ceilings. In the gradient-dominant branch the
complement cancellation regime is required; the curl-dominant branch uses
its own reversed ratio. Either branch gives the conditional smooth
continuation conclusion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Either admissible oriented ratio-escape branch, together with one
exponential physical ceiling, forces smooth continuation. -/
theorem positiveGrowth_orientedRatioEscape_extension_of_exponentialPhysicalCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (hEscape :
      (H3TerminalComplementCancellationRegime p sCurl sGradient ∧
        ∀ n : ℕ,
          (n : ℝ) + 1 <
            h3TerminalOrientedSelectedGradientLogForPair
                u p sGradient (τ (k n)) (y (k n)) /
              h3TerminalOrientedSelectedSignedCurlLogForPair
                u p sGradient (τ (k n)) (y (k n))) ∨
      (∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n))))
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
  rcases hEscape with ⟨hCancellation, hRatio⟩ | hRatio
  · exact positiveGrowth_gradientRatioEscape_extension_of_exponentialPhysicalCeiling
      hH3 hClass hb hg hData hCancellation hkTop hRatio
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Araw Agap Ad Aq
      rawDegree gapDegree dissipationDegree excessDegree hCeiling
  · exact positiveGrowth_curlRatioEscape_extension_of_exponentialPhysicalCeiling
      hH3 hClass hb hg hData hkTop hRatio
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Araw Agap Ad Aq
      rawDegree gapDegree dissipationDegree excessDegree hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
