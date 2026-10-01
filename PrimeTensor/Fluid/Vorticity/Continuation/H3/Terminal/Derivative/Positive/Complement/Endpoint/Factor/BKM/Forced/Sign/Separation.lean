import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Resolved.Finite.Alternative

/-!
# Sign separation in the forced endpoint complement branch

In the reinforcing sign regime, the selected gradient logarithm diverges
positively while the correctly signed selected curl logarithm diverges
negatively. The resolved endpoint alternative records this on the original
native sequence in its forced branch; its other branches are retained.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Reinforcing signs make the selected signed curl logarithm the negative
of the native curl logarithm in its fixed escape orientation. -/
theorem oriented_selectedSignedCurl_eq_neg_nativeCurl_of_forced
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (hForced : H3TerminalComplementForcedRegime p sCurl sGradient)
    (t : ℝ) (x : Point3) :
    h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient t x =
      -h3TerminalOrientedValue sCurl
        (PrimeTensor.Bridge.MulReal.logValue
          (h3TerminalNativeCurlForPair u p t x)) := by
  cases p <;> cases sCurl <;> cases sGradient <;>
    simp [H3TerminalComplementForcedRegime,
      h3TerminalOrientedSelectedSignedCurlLogForPair,
      h3TerminalSelectedCurlSignForPair,
      h3TerminalSelectedSignedNativeCurlLog,
      h3TerminalOrientedValue] at hForced ⊢

/-- Quantitative native growth places the signed curl below the negative
original index at every point of a forced-regime sequence. -/
theorem positiveGrowth_forced_signedCurl_below_negativeIndex
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hForced : H3TerminalComplementForcedRegime p sCurl sGradient) :
    ∀ n : ℕ,
      h3TerminalOrientedSelectedSignedCurlLogForPair
        u p sGradient (τ n) (y n) < -(n : ℝ) := by
  intro n
  have hCurl := (hData.1 n).2.2.2.1
  have hEq := oriented_selectedSignedCurl_eq_neg_nativeCurl_of_forced
    u p sCurl sGradient hForced (τ n) (y n)
  rw [hEq]
  linarith

/-- On the original forced-regime native sequence, the gradient log goes
to `+∞` and the correctly signed curl log goes to `-∞`. -/
theorem positiveGrowth_forced_selectedLogs_oppositeEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u b T p sCurl sGradient τ y)
    (hForced : H3TerminalComplementForcedRegime p sCurl sGradient) :
    Tendsto (fun n : ℕ =>
        h3TerminalOrientedSelectedGradientLogForPair
          u p sGradient (τ n) (y n)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        h3TerminalOrientedSelectedSignedCurlLogForPair
          u p sGradient (τ n) (y n)) atTop atBot := by
  constructor
  · refine tendsto_atTop.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hGradient := (hData.1 n).2.2.2.2
    change (n : ℝ) <
      h3TerminalOrientedSelectedGradientLogForPair
        u p sGradient (τ n) (y n) at hGradient
    linarith
  · refine tendsto_atBot.2 ?_
    intro M
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-M)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNCast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hCurl :=
      positiveGrowth_forced_signedCurl_below_negativeIndex hData hForced n
    linarith

/-- The full resolved endpoint alternative, with opposite selected-log
escapes explicitly attached to its forced branch. -/
def H3TerminalEndpointResolvedSignSeparatedAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (b T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
            u b T p sCurl sGradient τ y ∧
          ((H3TerminalComplementForcedRegime p sCurl sGradient ∧
              Tendsto (fun n : ℕ =>
                h3TerminalOrientedSelectedGradientLogForPair
                  u p sGradient (τ n) (y n)) atTop atTop ∧
              Tendsto (fun n : ℕ =>
                h3TerminalOrientedSelectedSignedCurlLogForPair
                  u p sGradient (τ n) (y n)) atTop atBot) ∨
           (∃ sComplement : H3TerminalOrientation,
              H3TerminalPositiveGrowthTripleNativeCascade
                u b T p sCurl sGradient sComplement ∧
              H3TerminalEndpointTripleFiniteRateData
                u b T p sCurl sGradient sComplement) ∨
           (H3TerminalComplementCancellationRegime p sCurl sGradient ∧
              H3TerminalPositiveGrowthBoundedComplementRatioAt
                u p sGradient τ y))

/-- Refine the forced branch of the resolved endpoint alternative on its
unchanged original native sequence. -/
theorem positiveGrowth_endpoint_resolvedSignSeparated_of_resolvedFinite
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {b T : ℝ}
    (hResolved : H3TerminalEndpointResolvedFiniteAlternative u b T) :
    H3TerminalEndpointResolvedSignSeparatedAlternative u b T := by
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hBranches⟩ := hResolved
  unfold H3TerminalEndpointResolvedSignSeparatedAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hBranches with hForced | hTriple | hBounded
  · exact Or.inl ⟨hForced.1,
      (positiveGrowth_forced_selectedLogs_oppositeEscape
        hData hForced.1).1,
      (positiveGrowth_forced_selectedLogs_oppositeEscape
        hData hForced.1).2⟩
  · exact Or.inr (Or.inl hTriple)
  · exact Or.inr (Or.inr hBounded)

/-- Hypothetical nonextension has a sign-separated resolved alternative
on every strict terminal subtail. -/
theorem positiveGrowth_endpoint_resolvedSignSeparated_on_every_subtail_of_noExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedSignSeparatedAlternative u b T := by
  intro b hb
  exact positiveGrowth_endpoint_resolvedSignSeparated_of_resolvedFinite
    (positiveGrowth_endpoint_resolvedFiniteAlternative_on_every_subtail_of_noExtension
      hH3 hNoExtension hClass b hb)

/-- Neutral continuation alternative with forced-branch sign separation
on every strict terminal subtail. -/
theorem smoothContinuationExtension_or_endpoint_resolvedSignSeparated_on_every_subtail
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    (∀ b : ℝ, b ∈ Set.Ioo a T →
      H3TerminalEndpointResolvedSignSeparatedAlternative u b T) := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_endpoint_resolvedSignSeparated_on_every_subtail_of_noExtension
        hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
