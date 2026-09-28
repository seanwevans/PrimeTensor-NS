import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEverySubtail

/-!
# Oriented ratio obstruction on each native endpoint subtail

Under hypothetical nonextension, quantitative native data can be selected
on every strict terminal subtail. If a selected sequence also has the
polynomial normalized growth ceiling, bounded normalized vorticity, and
an exponential ceiling for a physical rate, neither oriented ratio escape
condition from the continuation criterion can hold there.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The two oriented relative-ratio escape hypotheses of the endpoint
continuation criterion, with the cancellation regime on the gradient side. -/
def H3TerminalEndpointOrientedRatioEscapeData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ) (y : ℕ → Point3) (k : ℕ → ℕ) : Prop :=
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
          u p sGradient (τ (k n)) (y (k n)))

/-- Some fixed exponential polynomial square bounds one of the four
raw or normalized physical rates eventually on the original index. -/
def H3TerminalEndpointExponentialPhysicalCeilingData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (τ : ℕ → ℝ) : Prop :=
  ∃ Araw Agap Ad Aq : ℝ,
    ∃ rawDegree gapDegree dissipationDegree excessDegree : ℕ,
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
            Real.exp (Aq * (((i : ℝ) + 1) ^ excessDegree)) ^ 2))

/-- On a nonextending path, a native subtail with all three rate ceilings
cannot also have either oriented ratio escape. -/
theorem no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    {k : ℕ → ℕ}
    {g : ℝ → ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hg : ∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t)
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hkTop : Tendsto k atTop atTop)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    ¬ H3TerminalEndpointOrientedRatioEscapeData
        u p sCurl sGradient τ y k := by
  intro hEscape
  obtain ⟨Araw, Agap, Ad, Aq,
    rawDegree, gapDegree, dissipationDegree, excessDegree, hRate⟩ := hCeiling
  exact hNoExtension
    (positiveGrowth_orientedRatioEscape_extension_of_exponentialPhysicalCeiling
      hH3 hClass hb hg hData hkTop hEscape
      C growthDegree hGrowthCeiling B hVorticityCeiling
      Araw Agap Ad Aq
      rawDegree gapDegree dissipationDegree excessDegree hRate)

/-- Every strict subtail has an extracted native cascade on which any
cofinal ratio escape is excluded whenever the stated ceilings hold. -/
theorem exists_nativeSubtail_with_conditional_ratioObstruction_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∃ p : H3TerminalCurlGradientPair,
        ∃ sCurl sGradient : H3TerminalOrientation,
          ∃ τ : ℕ → ℝ,
            ∃ y : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              ∀ (k : ℕ → ℕ) (g : ℝ → ℝ),
                Tendsto k atTop atTop →
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
                    ¬ H3TerminalEndpointOrientedRatioEscapeData
                      u p sCurl sGradient τ y k := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  intro k g hkTop hg C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  exact no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
    hH3 hNoExtension hClass hb hg hData hkTop
    C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
