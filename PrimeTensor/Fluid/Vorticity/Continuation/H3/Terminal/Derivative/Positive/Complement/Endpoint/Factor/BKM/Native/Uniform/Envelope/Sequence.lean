import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Fixed.Actual.Vorticity.Envelope.Escape

/-!
# One native sequence for every terminal vorticity envelope

The pointwise actual-vorticity witness can be selected before choosing
an admissible scalar envelope. At those same times, every envelope
exceeds the native index threshold and tends to positive infinity.
The fixed component, structural pair, and orientations also work on
every strict terminal subtail. The subtail may change the sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A quantitative native sequence on each subtail has one fixed
actual-vorticity component escaping to infinity, and every envelope
on that subtail grows along the same sequence. The choice of times
precedes the universal quantifier over envelopes. -/
def H3TerminalPositiveGrowthUniformNativeEnvelopeRateData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ p : H3TerminalCurlGradientPair,
    ∃ sCurl sGradient : H3TerminalOrientation,
      ∃ i : Fin 3,
        ∀ b : ℝ, b ∈ Set.Ioo a T →
          ∃ τ : ℕ → ℝ,
            ∃ y z : ℕ → Point3,
              H3TerminalPositiveGrowthQuantitativeNativeData
                u b T p sCurl sGradient τ y ∧
              (∀ n : ℕ,
                (n : ℝ) - 2 <
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|) ∧
              Tendsto
                (fun n : ℕ =>
                  |h3NativeActualVorticityComponentAt u i (τ n) (z n)|)
                atTop atTop ∧
              ∀ g : ℝ → ℝ,
                (∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) →
                  (∀ n : ℕ, (n : ℝ) - 2 < g (τ n)) ∧
                  Tendsto (fun n : ℕ => g (τ n)) atTop atTop

/-- A globally fixed actual component provides one quantitative
native sequence per subtail that works simultaneously for all common
vorticity envelopes on that subtail. -/
theorem uniformNativeEnvelopeRate_of_globalFixedActualVorticity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hGlobal :
      H3TerminalPositiveGrowthGlobalFixedActualVorticityRateData u a T) :
    H3TerminalPositiveGrowthUniformNativeEnvelopeRateData u a T := by
  obtain ⟨p, sCurl, sGradient, i, hEvery⟩ := hGlobal
  refine ⟨p, sCurl, sGradient, i, ?_⟩
  intro b hb
  obtain ⟨τ, y, z, hData, hBound, hTop⟩ := hEvery b hb
  refine ⟨τ, y, z, hData, hBound, hTop, ?_⟩
  intro g hg
  have hEnvelopeBound : ∀ n : ℕ,
      |h3NativeActualVorticityComponentAt u i (τ n) (z n)| ≤
        g (τ n) := by
    intro n
    exact h3NativeActualVorticityComponentAt_le_vorticityEnvelope
      (hg (τ n) (hData.1 n).1) i (z n)
  constructor
  · intro n
    exact lt_of_lt_of_le (hBound n) (hEnvelopeBound n)
  · refine tendsto_atTop.2 ?_
    intro M
    filter_upwards [hTop.eventually (eventually_ge_atTop M)] with n hn
    exact le_trans hn (hEnvelopeBound n)

/-- Under hypothetical nonextension, a raw dissipation ceiling on
one chosen strict subtail forces the simultaneous native envelope
rate on every strict terminal subtail. -/
theorem positiveGrowth_uniformNativeEnvelopeRate_of_rawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    H3TerminalPositiveGrowthUniformNativeEnvelopeRateData u a T := by
  exact uniformNativeEnvelopeRate_of_globalFixedActualVorticity
    (positiveGrowth_globalFixedActualVorticity_of_rawCeiling_on_one_subtail
      hH3 hNoExtension hClass hb₀ hRawCeiling)

/-- Neutral continuation or a common native sequence for every
admissible envelope on each terminal subtail under the raw ceiling. -/
theorem smoothContinuationExtension_or_uniformNativeEnvelopeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    H3TerminalPositiveGrowthUniformNativeEnvelopeRateData u a T := by
  rcases
      smoothContinuationExtension_or_globalFixedActualVorticity_of_rawCeiling
        hH3 hClass hb₀ hRawCeiling with hExtension | hGlobal
  · exact Or.inl hExtension
  · exact Or.inr
      (uniformNativeEnvelopeRate_of_globalFixedActualVorticity hGlobal)

end

end Euclidean
end Bridge
end PrimeTensor
