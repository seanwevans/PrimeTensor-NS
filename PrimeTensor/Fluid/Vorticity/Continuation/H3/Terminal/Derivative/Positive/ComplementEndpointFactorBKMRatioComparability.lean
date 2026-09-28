import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMRatioBoundedness
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementRelativeBothNativeScale

/-!
# Endpoint comparability of the selected logarithms

In the complement cancellation regime, both selected logarithms are positive
on the quantitative native sequence. Eventual upper bounds for both ratios
therefore give a single constant comparing the two logarithms in each
direction under the physical endpoint ceilings.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Two eventually bounded ratios between positive sequences yield a
common eventual multiplicative comparison constant. -/
theorem eventual_comparability_of_two_ratio_bounds
    (A B : ℕ → ℝ)
    (hAPos : ∀ i : ℕ, 0 < A i)
    (hBPos : ∀ i : ℕ, 0 < B i)
    (hAB : ∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → A i / B i ≤ M)
    (hBA : ∃ M : ℝ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i → B i / A i ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      A i ≤ K * B i ∧ B i ≤ K * A i := by
  obtain ⟨MAB, NAB, hAB⟩ := hAB
  obtain ⟨MBA, NBA, hBA⟩ := hBA
  let K : ℝ := max 1 (max MAB MBA)
  have hKPos : 0 < K :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hMAB : MAB ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMBA : MBA ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hKPos, max NAB NBA, ?_⟩
  intro i hi
  have hiAB : NAB ≤ i := (le_max_left _ _).trans hi
  have hiBA : NBA ≤ i := (le_max_right _ _).trans hi
  constructor
  · exact (div_le_iff₀ (hBPos i)).mp ((hAB i hiAB).trans hMAB)
  · exact (div_le_iff₀ (hAPos i)).mp ((hBA i hiBA).trans hMBA)

/-- Under hypothetical nonextension and the endpoint ceilings, the two
selected logs in the cancellation regime have the same eventual scale up
to one positive constant. -/
theorem positiveGrowth_endpoint_selectedLogs_comparable_of_exponentialCeiling
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
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient)
    (C : ℝ) (growthDegree : ℕ)
    (hGrowthCeiling : ∀ᶠ i : ℕ in atTop,
      deriv (velocityH3EnergyAt u) (τ i) /
          velocityH3EnergyAt u (τ i) ≤
        C * (((i : ℝ) + 1) ^ growthDegree))
    (B : ℝ)
    (hVorticityCeiling : ∀ᶠ i : ℕ in atTop,
      (1 + |g (τ i)|) ^ 2 / ((i : ℝ) + 1) ≤ B)
    (hCeiling : H3TerminalEndpointExponentialPhysicalCeilingData u τ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ i) (y i) ≤
        K * h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ i) (y i) ∧
      h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ i) (y i) ≤
        K * h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ i) (y i) := by
  have hBounds :=
    positiveGrowth_endpoint_orientedRatio_eventuallyBounded_of_exponentialCeiling
      hH3 hNoExtension hClass hb hg hData
      C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling
  have hGradientPos : ∀ i : ℕ,
      0 < h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ i) (y i) := by
    intro i
    have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact lt_of_le_of_lt hiNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation i).1
  have hCurlPos : ∀ i : ℕ,
      0 < h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ i) (y i) := by
    intro i
    have hiNonneg : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    exact lt_of_le_of_lt hiNonneg
      (positiveGrowth_selectedLogs_above_originalIndex_of_cancellation
        hData hCancellation i).2
  exact eventual_comparability_of_two_ratio_bounds
    (fun i => h3TerminalOrientedSelectedGradientLogForPair
      u p sGradient (τ i) (y i))
    (fun i => h3TerminalOrientedSelectedSignedCurlLogForPair
      u p sGradient (τ i) (y i))
    hGradientPos hCurlPos (hBounds.2 hCancellation) hBounds.1

/-- The conditional two-sided comparison is available on a native sequence
selected inside every strict terminal subtail. -/
theorem exists_nativeSubtail_with_conditional_selectedLogs_comparability_of_noExtension
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
                    H3TerminalComplementCancellationRegime p sCurl sGradient →
                    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
                      h3TerminalOrientedSelectedGradientLogForPair
                          u p sGradient (τ i) (y i) ≤
                        K * h3TerminalOrientedSelectedSignedCurlLogForPair
                          u p sGradient (τ i) (y i) ∧
                      h3TerminalOrientedSelectedSignedCurlLogForPair
                          u p sGradient (τ i) (y i) ≤
                        K * h3TerminalOrientedSelectedGradientLogForPair
                          u p sGradient (τ i) (y i) := by
  intro b hb
  obtain ⟨p, sCurl, sGradient, τ, y, hData⟩ :=
    positiveGrowth_quantitativeNativeData_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  intro g hg C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling hCancellation
  exact positiveGrowth_endpoint_selectedLogs_comparable_of_exponentialCeiling
    hH3 hNoExtension hClass hb hg hData hCancellation
    C growthDegree hGrowthCeiling B hVorticityCeiling hCeiling

end

end Euclidean
end Bridge
end PrimeTensor
