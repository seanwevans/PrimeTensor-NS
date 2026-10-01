import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Ratio.Recurrence

/-!
# Eventual bounds for endpoint oriented ratios

Excluding ratio escape along every cofinal reindexing rules out arbitrarily
large late spikes. Thus each admissible oriented ratio is eventually bounded
above by a fixed real number under the endpoint physical ceilings.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Arbitrarily high late spikes can be selected cofinally. Consequently,
failure of ratio escape on every cofinal reindexing gives an eventual
constant upper bound on the original sequence. -/
theorem ratio_eventually_bounded_of_no_cofinal_escape
    (R : ℕ → ℝ)
    (hNoEscape : ∀ k : ℕ → ℕ,
      Tendsto k atTop atTop →
        ¬ ∀ n : ℕ, (n : ℝ) + 1 < R (k n)) :
    ∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → R i ≤ M := by
  classical
  by_contra hBound
  push_neg at hBound
  let k : ℕ → ℕ := fun n => Classical.choose (hBound ((n : ℝ) + 1) n)
  have hk (n : ℕ) : n ≤ k n ∧ (n : ℝ) + 1 < R (k n) := by
    exact Classical.choose_spec (hBound ((n : ℝ) + 1) n)
  have hkTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with n hn
    exact hn.trans (hk n).1
  exact hNoEscape k hkTop (fun n => (hk n).2)

/-- On a nonextending native endpoint sequence, the physical ceilings
force the curl-over-gradient ratio to be eventually bounded. In the
complement cancellation regime they also bound the reverse ratio. -/
theorem positiveGrowth_endpoint_orientedRatio_eventuallyBounded_of_exponentialCeiling
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
    (∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ i) (y i) /
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ i) (y i) ≤ M) ∧
    (H3TerminalComplementCancellationRegime p sCurl sGradient →
      ∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
        h3TerminalOrientedSelectedGradientLogForPair
            u p sGradient (τ i) (y i) /
          h3TerminalOrientedSelectedSignedCurlLogForPair
            u p sGradient (τ i) (y i) ≤ M) := by
  constructor
  · apply ratio_eventually_bounded_of_no_cofinal_escape
    intro k hkTop hRatio
    have hNoEscape := no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hkTop
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
    exact hNoEscape (Or.inr hRatio)
  · intro hCancellation
    apply ratio_eventually_bounded_of_no_cofinal_escape
    intro k hkTop hRatio
    have hNoEscape := no_orientedRatioEscape_of_noExtension_and_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData hkTop
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
    exact hNoEscape (Or.inl ⟨hCancellation, hRatio⟩)

/-- Every strict terminal subtail admits native data whose oriented ratios
have eventual constant upper bounds whenever the stated ceilings hold. -/
theorem exists_nativeSubtail_with_conditional_orientedRatio_boundedness_of_noExtension
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
                    (∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
                      h3TerminalOrientedSelectedSignedCurlLogForPair
                          u p sGradient (τ i) (y i) /
                        h3TerminalOrientedSelectedGradientLogForPair
                          u p sGradient (τ i) (y i) ≤ M) ∧
                    (H3TerminalComplementCancellationRegime p sCurl sGradient →
                      ∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
                        h3TerminalOrientedSelectedGradientLogForPair
                            u p sGradient (τ i) (y i) /
                          h3TerminalOrientedSelectedSignedCurlLogForPair
                            u p sGradient (τ i) (y i) ≤ M) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  intro g hg C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  exact positiveGrowth_endpoint_orientedRatio_eventuallyBounded_of_exponentialCeiling
    hH3 hNoExtension hClass hb hg hData
    C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
