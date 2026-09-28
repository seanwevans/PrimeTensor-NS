import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMSubtailRatioObstruction

/-!
# Recurrent limits on endpoint oriented ratios

Failure of ratio escape after every cofinal reindexing gives a concrete
original-index statement: arbitrarily far out, the ratio is no larger than
the index plus one. Under the physical ceilings this applies to the
curl-over-gradient ratio, and also to the reverse ratio in the complement
cancellation regime.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- If no cofinal reindexing has a ratio above its new index at every
point, then the original ratio falls below its index arbitrarily late. -/
theorem ratio_recurrence_of_no_cofinal_escape
    (R : ℕ → ℝ)
    (hNoEscape : ∀ k : ℕ → ℕ,
      Tendsto k atTop atTop →
        ¬ ∀ n : ℕ, (n : ℝ) + 1 < R (k n)) :
    ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧ R i ≤ (i : ℝ) + 1 := by
  classical
  intro N
  let k : ℕ → ℕ := fun n => n + N
  have hkTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    dsimp [k]
    omega
  have hFailure := hNoEscape k hkTop
  push_neg at hFailure
  obtain ⟨n, hn⟩ := hFailure
  refine ⟨k n, ?_, ?_⟩
  · dsimp [k]
    omega
  · have hIndex : n ≤ k n := by
      dsimp [k]
      omega
    have hCast : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hIndex
    exact hn.trans (by linarith)

/-- Under hypothetical nonextension and the three endpoint ceilings,
curl-over-gradient ratio recurrence is necessary; gradient-over-curl
recurrence is necessary in the cancellation regime. -/
theorem positiveGrowth_endpoint_orientedRatio_recurrence_of_exponentialCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
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
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    (∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ i) (y i) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ i) (y i) ≤ (i : ℝ) + 1) ∧
    (H3TerminalComplementCancellationRegime p sCurl sGradient →
      ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i) ≤ (i : ℝ) + 1) := by
  constructor
  · apply ratio_recurrence_of_no_cofinal_escape
    intro k hkTop hRatio
    have hNoEscape := no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hkTop
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
    exact hNoEscape (Or.inr hRatio)
  · intro hCancellation
    apply ratio_recurrence_of_no_cofinal_escape
    intro k hkTop hRatio
    have hNoEscape := no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hkTop
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
    exact hNoEscape (Or.inl ⟨hCancellation, hRatio⟩)

/-- Every strict terminal subtail has a native sequence for which the
physical ceilings force arbitrarily late oriented-ratio bounds. -/
theorem exists_nativeSubtail_with_conditional_orientedRatio_recurrence_of_noExtension
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
                    (∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧
                      h3TerminalOrientedSelectedSignedCurlLogForPair
                          u p sGradient (τ i) (y i) /
                        h3TerminalOrientedSelectedGradientLogForPair
                          u p sGradient (τ i) (y i) ≤ (i : ℝ) + 1) ∧
                    (H3TerminalComplementCancellationRegime p sCurl sGradient →
                      ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧
                        h3TerminalOrientedSelectedGradientLogForPair
                            u p sGradient (τ i) (y i) /
                          h3TerminalOrientedSelectedSignedCurlLogForPair
                            u p sGradient (τ i) (y i) ≤ (i : ℝ) + 1) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  intro g hg C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  exact positiveGrowth_endpoint_orientedRatio_recurrence_of_exponentialCeiling
    hH3 hNoExtension hClass hb hg hData
    C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
