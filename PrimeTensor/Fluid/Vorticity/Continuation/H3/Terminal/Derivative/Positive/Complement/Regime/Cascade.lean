import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Quantitative.Native.Cascade
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Complementary.Gradient.Dichotomy

/-!
# Complementary-gradient regimes on the positive-growth cascade

The quantitative native cascade already carries a fixed structural pair, fixed
orientations, and one common sequence of times and points.  This file applies
the exact complementary-gradient sign split to those very same witnesses.

In the reinforcing regime, the complementary native logarithm exceeds `2n`
and escapes in the selected-gradient orientation on the positive-growth
sequence.  In the other regime the statement records cancellation compatibility
without asserting complementary escape.  The full H³ scalar and frequency
limits remain attached to the witness in either case.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- All the data carried by one quantitative positive-growth native cascade. -/
def H3TerminalPositiveGrowthQuantitativeNativeData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ)
    (p : H3TerminalCurlGradientPair)
    (sCurl sGradient : H3TerminalOrientation)
    (τ : ℕ → ℝ)
    (y : ℕ → Point3) : Prop :=
  (∀ n : ℕ,
      τ n ∈ Set.Ioo a T
        ∧
      τ n ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T
        ∧
      (n : ℝ) < deriv (velocityH3EnergyAt u) (τ n)
        ∧
      (n : ℝ) <
        h3TerminalOrientedValue sCurl
          (PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeCurlForPair u p (τ n) (y n)))
        ∧
      (n : ℝ) <
        h3TerminalOrientedValue sGradient
          (PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeGradientForPair u p (τ n) (y n))))
    ∧
  Tendsto τ atTop (𝓝 T)
    ∧
  Tendsto (fun n : ℕ => velocityH3EnergyAt u (τ n)) atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        velocityH3DissipationAt u (τ n) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ =>
        (-velocityH3TransportDerivativeAt u (τ n)) /
          velocityH3EnergyAt u (τ n))
      atTop atTop
    ∧
  Tendsto
      (fun n : ℕ => h3TopCharacteristicFrequencyAt u (τ n))
      atTop atTop
    ∧
  H3TerminalNativeLogDirectionalEscape
      (fun n : ℕ => h3TerminalNativeCurlForPair u p (τ n) (y n))
      sCurl
    ∧
  H3TerminalNativeLogDirectionalEscape
      (fun n : ℕ => h3TerminalNativeGradientForPair u p (τ n) (y n))
      sGradient
    ∧
  H3TerminalNativeCurlGradientDoubleDirectionalEscape
      u a T p sCurl sGradient

/-- The sign split together with the complete, common positive-growth witness. -/
def H3TerminalPositiveGrowthNativeComplementAlternative
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
            H3TerminalComplementCancellationRegime p sCurl sGradient)

/-- Hypothetical nonextension yields the complementary sign alternative on
the *same* positive-growth time and point sequence. -/
theorem positiveGrowth_nativeComplementAlternative_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    H3TerminalPositiveGrowthNativeComplementAlternative u a T := by
  classical
  obtain ⟨p, sCurl, sGradient, τ, y,
      hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
      hCurlEscape, hGradientEscape, hDirectional⟩ :=
    exists_terminal_positiveGrowth_fullCascade_quantitativeNativeDoubleEscape_of_noH3PathExtension
      hH3 hNoExtension hClass hb

  have hData :
      H3TerminalPositiveGrowthQuantitativeNativeData
        u a T p sCurl sGradient τ y := by
    exact ⟨hAt, hTau, hEnergy, hDiss, hTransport, hFrequency,
      hCurlEscape, hGradientEscape, hDirectional⟩

  unfold H3TerminalPositiveGrowthNativeComplementAlternative
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
        (hAt n).2.2.2.1 (hAt n).2.2.2.2

    have hComplementTendsto :
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
              u p (τ n) (y n))
          sGradient := by
      exact nativeLogDirectionalEscape_of_oriented_log_bridge
        (Ω := fun n : ℕ =>
          h3TerminalNativeComplementGradientForPair
            u p (τ n) (y n))
        (H := fun n : ℕ =>
          PrimeTensor.Bridge.MulReal.logValue
            (h3TerminalNativeComplementGradientForPair
              u p (τ n) (y n)))
        (s := sGradient)
        (fun n => rfl)
        hComplementTendsto

    exact Or.inl ⟨hForced, hComplementBound, hComplementEscape⟩
  · exact Or.inr hForced

/-- Neutral continuation alternative with all cascade limits retained in
either complementary-gradient sign regime. -/
theorem smoothContinuationExtension_or_positiveGrowth_nativeComplementAlternative
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb : b ∈ Set.Ioo a T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T)
      ∨
    H3TerminalPositiveGrowthNativeComplementAlternative u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (positiveGrowth_nativeComplementAlternative_of_noH3PathExtension
        hH3 hExtension hClass hb)

end

end Euclidean
end Bridge
end PrimeTensor
