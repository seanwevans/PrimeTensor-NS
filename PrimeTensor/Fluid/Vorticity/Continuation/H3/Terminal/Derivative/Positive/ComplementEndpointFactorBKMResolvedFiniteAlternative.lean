import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMTripleFiniteRate
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ResolvedComplementCascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeEverySubtail

/-!
# Resolved complement alternative with conditional finite endpoint rates

The forced complement and bounded complement branches remain as in the
resolved native alternative. Its triple native branch now records a second
selected witness: under the growth, vorticity, and physical ceilings on
that witness, the two finite relative-rate outcomes are available.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A selected triple native witness whose endpoint ceilings imply the
matching-or-finite-separation dichotomy. -/
def H3TerminalEndpointTripleFiniteRateData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient sComplement : H3TerminalOrientation) : Prop :=
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
              u b T p sCurl sGradient sComplement τ y

/-- The three resolved complement branches, with conditional finite-rate
data attached to the triple native branch. -/
def H3TerminalEndpointResolvedFiniteAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient τ y ∧
          ((H3TerminalComplementForcedRegime p sCurl sGradient ∧
              (∀ n : ℕ,
                2 * (n : ℝ) <
                  h3TerminalOrientedValue sGradient
                    (PrimeTensor.Bridge.MulReal.logValue
                      (h3TerminalNativeComplementGradientForPair
                        u p (τ n) (y n)))) ∧
              H3TerminalNativeLogDirectionalEscape
                (fun n : ℕ =>
                  h3TerminalNativeComplementGradientForPair
                    u p (τ n) (y n)) sGradient) ∨
           (∃ sComplement : H3TerminalOrientation,
              H3TerminalPositiveGrowthTripleNativeCascade
                u b T p sCurl sGradient sComplement ∧
              H3TerminalEndpointTripleFiniteRateData
                u b T p sCurl sGradient sComplement) ∨
           (H3TerminalComplementCancellationRegime p sCurl sGradient ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine a resolved complement alternative on a strict terminal subtail.
The triple branch obtains finite relative-rate data conditional on its
selected sequence satisfying the endpoint ceilings. -/
theorem positiveGrowth_endpoint_resolvedFiniteAlternative_of_resolved
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T)
    (hResolved :
      H3TerminalPositiveGrowthResolvedComplementAlternative u b T) :
    H3TerminalEndpointResolvedFiniteAlternative u b T := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalEndpointResolvedFiniteAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hTriple | hBounded
  · exact Or.inl hForced
  · obtain ⟨sComplement, hTriple⟩ := hTriple
    have hFinite :
        H3TerminalEndpointTripleFiniteRateData
          u b T p sCurl sGradient sComplement :=
      positiveGrowth_tripleNative_endpoint_finiteRateDichotomy_of_exponentialCeiling
        hH3 hNoExtension hClass hb hTriple
    exact Or.inr (Or.inl ⟨sComplement, hTriple, hFinite⟩)
  · exact Or.inr (Or.inr hBounded)

/-- Resolve the complement sign and tail-size alternatives directly from
quantitative native data already placed on the chosen subtail. -/
theorem positiveGrowth_resolvedComplement_of_quantitativeNativeData
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y) :
    H3TerminalPositiveGrowthResolvedComplementAlternative u b T := by
  classical
  have hAlternative :
      H3TerminalPositiveGrowthNativeComplementRatioAlternative u b T := by
    unfold H3TerminalPositiveGrowthNativeComplementRatioAlternative
    refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
    by_cases hForced :
        H3TerminalComplementForcedRegime p sCurl sGradient
    · have hComplementBound :
          ∀ n : ℕ,
            2 * (n : ℝ) <
              h3TerminalOrientedValue sGradient
                (PrimeTensor.Bridge.MulReal.logValue
                  (h3TerminalNativeComplementGradientForPair
                    u p (τ n) (y n))) := by
        intro n
        exact two_mul_natCast_lt_oriented_complement_of_forcedRegime
          u p sCurl sGradient hForced n (τ n) (y n)
          (hData.1 n).2.2.2.1 (hData.1 n).2.2.2.2
      have hComplementTop :
          Tendsto
            (fun n : ℕ =>
              h3TerminalOrientedValue sGradient
                (PrimeTensor.Bridge.MulReal.logValue
                  (h3TerminalNativeComplementGradientForPair
                    u p (τ n) (y n))))
            atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro M
        obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (M / 2)
        filter_upwards [eventually_ge_atTop N] with n hn
        have hNLe : (N : ℝ) ≤ n := by exact_mod_cast hn
        have hMlt : M < 2 * (n : ℝ) := by linarith
        exact le_of_lt (lt_trans hMlt (hComplementBound n))
      have hComplementEscape :
          H3TerminalNativeLogDirectionalEscape
            (fun n : ℕ =>
              h3TerminalNativeComplementGradientForPair
                u p (τ n) (y n)) sGradient := by
        exact nativeLogDirectionalEscape_of_oriented_log_bridge
          (Ω := fun n : ℕ =>
            h3TerminalNativeComplementGradientForPair
              u p (τ n) (y n))
          (H := fun n : ℕ =>
            PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeComplementGradientForPair
                u p (τ n) (y n)))
          (s := sGradient)
          (fun n => rfl) hComplementTop
      exact Or.inl ⟨hForced, hComplementBound, hComplementEscape⟩
    · exact Or.inr
        (positiveGrowth_cancellationRatioAt_of_data hData hForced)
  exact positiveGrowth_resolvedComplement_of_ratioAlternative hAlternative

/-- On every strict terminal subtail, hypothetical nonextension yields
the exhaustive complement alternative with conditional finite-rate data
in its triple native branch. -/
theorem positiveGrowth_endpoint_resolvedFiniteAlternative_on_every_subtail_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedFiniteAlternative u b T := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  have hResolved :
      H3TerminalPositiveGrowthResolvedComplementAlternative u b T :=
    positiveGrowth_resolvedComplement_of_quantitativeNativeData hData
  exact positiveGrowth_endpoint_resolvedFiniteAlternative_of_resolved
    hH3 hNoExtension hClass hb hResolved

/-- Neutral continuation formulation of the refined endpoint alternative
on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_endpoint_resolvedFiniteAlternative_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedFiniteAlternative u b T) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_endpoint_resolvedFiniteAlternative_on_every_subtail_of_noExtension
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
