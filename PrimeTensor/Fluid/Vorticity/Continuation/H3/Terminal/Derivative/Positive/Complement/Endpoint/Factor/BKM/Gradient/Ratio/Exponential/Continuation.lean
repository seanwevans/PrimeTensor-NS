import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Exponential.Continuation

/-!
# Gradient-ratio escape and exponential physical continuation

On the gradient-dominant cancellation branch, a quantitative native cascade
and its strict oriented ratio inequality produce the relative refined
endpoint witness if smooth continuation fails. The exponential physical
ceiling criterion then contradicts that failure. This formulation takes
the native and ratio conditions directly instead of assuming the derived
refined witness.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A gradient-dominant quantitative native cascade with ratio escape
and one exponential physical ceiling forces smooth continuation. -/
theorem positiveGrowth_gradientRatioEscape_extension_of_exponentialPhysicalCeiling
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
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (hkTop : Tendsto k atTop atTop)
    (hRatio :
      ∀ n : ℕ,
        (n : ℝ) + 1 <
          h3TerminalOrientedSelectedGradientLogForPair
              u p sGradient (τ (k n)) (y (k n)) /
            h3TerminalOrientedSelectedSignedCurlLogForPair
              u p sGradient (τ (k n)) (y (k n)))
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
  have hWitness :=
    positiveGrowth_gradientRatioEscape_endpoint_relativeRefinedWitness
      hH3 hNoExtension hClass hb hg hData hCancellation hkTop hRatio
  exact hNoExtension
    (endpointFactor_relativeRefinedWitness_extension_of_exponentialPhysicalCeiling
      hH3 hClass hb hg hWitness
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Araw Agap Ad Aq
      rawDegree gapDegree dissipationDegree excessDegree hCeiling)

end

end Euclidean
end Bridge
end PrimeTensor
