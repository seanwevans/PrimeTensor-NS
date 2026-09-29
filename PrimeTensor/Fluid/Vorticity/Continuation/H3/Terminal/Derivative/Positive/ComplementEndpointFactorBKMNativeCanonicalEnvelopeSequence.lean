import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeUniformEnvelopeSequence
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ActualVorticitySynchronization

/-!
# Canonical physical vorticity envelope on the native endpoint sequence

The minimal common upper bound of the three actual vorticity components
is a genuine vorticity envelope on every strict H³-path slice. Thus the
simultaneous envelope sequence has a concrete canonical instance: the
minimal envelope exceeds `n - 2` and tends to infinity along the same
times as the selected fixed actual component.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- A fixed actual vorticity component and the canonical minimal
vorticity envelope escape together on a quantitative native sequence
on every strict terminal subtail. -/
def H3TerminalPositiveGrowthCanonicalEnvelopeRateData
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
              (∀ n : ℕ,
                (n : ℝ) - 2 <
                  h3MinimalVorticityEnvelopeAt u (τ n)) ∧
              Tendsto
                (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
                atTop atTop

/-- The canonical minimal envelope is admissible at each selected
preterminal time, so the universal native envelope rate applies to it. -/
theorem canonicalEnvelopeRate_of_uniformNativeEnvelopeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hUniform :
      H3TerminalPositiveGrowthUniformNativeEnvelopeRateData u a T) :
    H3TerminalPositiveGrowthCanonicalEnvelopeRateData u a T := by
  obtain ⟨p, sCurl, sGradient, i, hEvery⟩ := hUniform
  refine ⟨p, sCurl, sGradient, i, ?_⟩
  intro b hb
  obtain ⟨τ, y, z, hData, hBound, hTop, hAll⟩ := hEvery b hb
  have hg : ∀ t : ℝ, t ∈ Set.Ioo b T →
      VorticityEnvelope u (h3MinimalVorticityEnvelopeAt u) t := by
    intro t ht
    have ht0 : t ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_trans (lt_trans hClass.terminal_start.1 hb.1) ht.1,
        ht.2⟩
    exact vorticityEnvelope_h3MinimalVorticityEnvelopeAt hH3 ht0
  obtain ⟨hCanonicalRate, hCanonicalTop⟩ :=
    hAll (h3MinimalVorticityEnvelopeAt u) hg
  exact ⟨τ, y, z, hData, hBound, hTop,
    hCanonicalRate, hCanonicalTop⟩

/-- Under hypothetical nonextension and the raw dissipation ceiling
on one strict subtail, the canonical minimal envelope has the
indexed native rate on every strict terminal subtail. -/
theorem positiveGrowth_canonicalEnvelopeRate_of_rawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    H3TerminalPositiveGrowthCanonicalEnvelopeRateData u a T := by
  exact canonicalEnvelopeRate_of_uniformNativeEnvelopeRate hH3 hClass
    (positiveGrowth_uniformNativeEnvelopeRate_of_rawCeiling
      hH3 hNoExtension hClass hb₀ hRawCeiling)

/-- Neutral continuation or a common fixed-component and canonical
vorticity-envelope rate under the stated raw ceiling. -/
theorem smoothContinuationExtension_or_canonicalEnvelopeRate
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    H3TerminalPositiveGrowthCanonicalEnvelopeRateData u a T := by
  rcases
      smoothContinuationExtension_or_uniformNativeEnvelopeRate
        hH3 hClass hb₀ hRawCeiling with hExtension | hUniform
  · exact Or.inl hExtension
  · exact Or.inr
      (canonicalEnvelopeRate_of_uniformNativeEnvelopeRate
        hH3 hClass hUniform)

end

end Euclidean
end Bridge
end PrimeTensor
