import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Regime.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Complementary.Gradient.Cancellation.Ratio

/-!
# Cancellation refinement on the positive-growth native cascade

The complementary sign split on the positive-growth cascade retains one fixed
pair, two fixed orientations, and the original time and point sequence.  In its
cancellation-compatible branch, the complementary logarithm is either
tail-cofinally unbounded in one orientation, or eventually bounded in
magnitude.  The bounded case gives an exact bounded defect and a ratio-one
limit for the correctly oriented selected-gradient and signed-curl logarithms.

Every alternative here uses the same sequence that carries the full H³ energy,
normalized dissipation, adverse-transport, and characteristic-frequency limits.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The two exhaustive outcomes for the complementary logarithm in the
cancellation-compatible sign regime, on the given positive-growth sequence. -/
def H3TerminalPositiveGrowthComplementCancellationRatioAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  H3TerminalComplementCancellationRegime p sCurl sGradient
    ∧
  ((∃ sComplement : H3TerminalOrientation,
      H3TerminalScalarSeqOrientedTailCofinallyUnbounded
        (fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeComplementGradientForPair
              u p (τ n) (y n)))
        sComplement)
    ∨
    (∃ N : ℕ,
      ∃ C : ℝ,
        (∀ n : ℕ,
          N ≤ n →
            abs
              (PrimeTensor.Bridge.MulReal.logValue
                (h3TerminalNativeComplementGradientForPair
                  u p (τ n) (y n))) ≤ C
              ∧
            abs
              (PrimeTensor.Bridge.MulReal.logValue
                (h3TerminalNativeGradientForPair
                  u p (τ n) (y n))
                - h3TerminalSelectedSignedNativeCurlLog
                    u p (τ n) (y n)) ≤ C)
          ∧
        Tendsto
          (fun n : ℕ =>
            h3TerminalOrientedValue sGradient
                (PrimeTensor.Bridge.MulReal.logValue
                  (h3TerminalNativeGradientForPair
                    u p (τ n) (y n))) /
              h3TerminalOrientedValue sGradient
                (h3TerminalSelectedSignedNativeCurlLog
                  u p (τ n) (y n)))
          atTop (𝓝 1)))

/-- A cancellation-compatible quantitative cascade has the exhaustive
complementary alternative on its original time and point sequence. -/
theorem positiveGrowth_cancellationRatioAt_of_data
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    {p : H3TerminalCurlGradientPair}
    {sCurl sGradient : H3TerminalOrientation}
    {τ : ℕ → ℝ}
    {y : ℕ → Point3}
    (hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y)
    (hCancellation :
      H3TerminalComplementCancellationRegime p sCurl sGradient) :
    H3TerminalPositiveGrowthComplementCancellationRatioAt
      u p sCurl sGradient τ y := by
  classical
  have hCurlEscape :
      H3TerminalNativeLogDirectionalEscape
        (fun n : ℕ =>
          h3TerminalNativeCurlForPair u p (τ n) (y n))
        sCurl := by
    rcases hData with ⟨_, _, _, _, _, _, hCurlEscape, _, _⟩
    exact hCurlEscape

  let f : ℕ → ℝ :=
    fun n : ℕ =>
      PrimeTensor.Bridge.MulReal.logValue
        (h3TerminalNativeComplementGradientForPair
          u p (τ n) (y n))

  unfold H3TerminalPositiveGrowthComplementCancellationRatioAt
  refine ⟨hCancellation, ?_⟩
  rcases scalarSeq_absTailCofinallyUnbounded_or_eventuallyAbsBounded f
    with hUnbounded | hBounded
  · obtain ⟨sComplement, hOriented⟩ :=
      exists_orientation_of_scalarSeq_absTailCofinallyUnbounded
        hUnbounded
    exact Or.inl ⟨sComplement, hOriented⟩
  · obtain ⟨N, C, hBound⟩ := hBounded
    have hDefect :
        ∀ n : ℕ,
          N ≤ n →
          abs
            (PrimeTensor.Bridge.MulReal.logValue
              (h3TerminalNativeGradientForPair
                u p (τ n) (y n))
              - h3TerminalSelectedSignedNativeCurlLog
                  u p (τ n) (y n)) ≤ C := by
      intro n hn
      rw [← logValue_nativeComplement_eq_gradient_sub_signedCurl
        u p (τ n) (y n)]
      exact hBound n hn

    have hRatio :
        Tendsto
          (fun n : ℕ =>
            h3TerminalOrientedValue sGradient
                (PrimeTensor.Bridge.MulReal.logValue
                  (h3TerminalNativeGradientForPair
                    u p (τ n) (y n))) /
              h3TerminalOrientedValue sGradient
                (h3TerminalSelectedSignedNativeCurlLog
                  u p (τ n) (y n)))
          atTop (𝓝 1) :=
      cancellationMatchedRatio_tendsto_one
        hCancellation hCurlEscape (N := N) (C := C) hDefect

    exact Or.inr
      ⟨N, C, (fun n hn => ⟨hBound n hn, hDefect n hn⟩), hRatio⟩

/-- The forced branch is retained, while the cancellation branch is refined
without changing the quantitative positive-growth witness. -/
def H3TerminalPositiveGrowthNativeComplementRatioAlternative
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ y : ℕ → Point3,
          H3TerminalPositiveGrowthQuantitativeNativeData
              u a T p sCurl sGradient τ y
            ∧
          ((H3TerminalComplementForcedRegime p sCurl sGradient
              ∧
            (∀ n : ℕ,
              2 * (n : ℝ) <
                h3TerminalOrientedValue sGradient
                  (PrimeTensor.Bridge.MulReal.logValue
                    (h3TerminalNativeComplementGradientForPair
                      u p (τ n) (y n))))
              ∧
            H3TerminalNativeLogDirectionalEscape
              (fun n : ℕ =>
                h3TerminalNativeComplementGradientForPair
                  u p (τ n) (y n))
              sGradient)
            ∨
            H3TerminalPositiveGrowthComplementCancellationRatioAt
              u p sCurl sGradient τ y)

/-- Conditional nonextension gives the ratio-refined complementary
alternative along the full positive-growth native cascade. -/
theorem positiveGrowth_nativeComplementRatioAlternative_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthNativeComplementRatioAlternative u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y, hData, hAlternative⟩ :=
    positiveGrowth_nativeComplementAlternative_of_noH3PathExtension
      hH3 hNoExtension hClass hb
  unfold H3TerminalPositiveGrowthNativeComplementRatioAlternative
  refine ⟨p, sCurl, sGradient, τ, y, hData, ?_⟩
  rcases hAlternative with hForced | hCancellation
  · exact Or.inl hForced
  · exact Or.inr
      (positiveGrowth_cancellationRatioAt_of_data
        hData hCancellation)

/-- Neutral continuation formulation of the ratio-refined cascade. -/
theorem smoothContinuationExtension_or_positiveGrowth_nativeComplementRatioAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthNativeComplementRatioAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_nativeComplementRatioAlternative_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
