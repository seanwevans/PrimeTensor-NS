import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Fixed.Actual.Vorticity.Endpoint.Escape

/-!
# Transferring fixed actual-vorticity escape to every envelope

An admissible scalar vorticity envelope bounds each actual vorticity
component at every spatial point. The fixed-component endpoint escape
therefore forces the same indexed near-terminal lower values in every
envelope, as well as unbounded envelope values on each strict subtail.
This is a pointwise statement and does not assert nonintegrability.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- Every common vorticity envelope bounds a selected actual component. -/
theorem h3NativeActualVorticityComponentAt_le_vorticityEnvelope
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {g : ℝ → ℝ} {t : ℝ}
    (hEnvelope : VorticityEnvelope u g t)
    (i : Fin 3) (x : Point3) :
    |h3NativeActualVorticityComponentAt u i t x| ≤ g t := by
  by_cases hx : i = 0
  · simpa [h3NativeActualVorticityComponentAt, hx] using (hEnvelope x).1
  by_cases hy : i = 1
  · simpa [h3NativeActualVorticityComponentAt, hx, hy] using (hEnvelope x).2.1
  · simpa [h3NativeActualVorticityComponentAt, hx, hy] using (hEnvelope x).2.2

/-- The same fixed component forces every common envelope to attain
indexed lower values in terminal windows and arbitrarily large values
on every strict subtail. The time can depend on the envelope. -/
def H3TerminalEveryVorticityEnvelopeEndpointEscape
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∃ i : Fin 3,
    ∀ b : ℝ, b ∈ Set.Ioo a T →
      ∀ g : ℝ → ℝ,
        (∀ t : ℝ, t ∈ Set.Ioo b T → VorticityEnvelope u g t) →
          (∀ n : ℕ,
            ∃ t : ℝ,
              t ∈ Set.Ioo b T ∧
              t ∈ Set.Ioo (T - (1 : ℝ) / ((n : ℝ) + 1)) T ∧
              (n : ℝ) - 2 < g t) ∧
          (∀ M : ℝ,
            ∃ t : ℝ,
              t ∈ Set.Ioo b T ∧ M < g t)

/-- Pointwise escape of an actual component transfers to each
admissible common vorticity envelope on the same terminal subtail. -/
theorem everyVorticityEnvelope_endpointEscape_of_fixedActualVorticity
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {a T : ℝ}
    (hEscape : H3TerminalFixedActualVorticityEndpointEscape u a T) :
    H3TerminalEveryVorticityEnvelopeEndpointEscape u a T := by
  obtain ⟨i, hEvery⟩ := hEscape
  refine ⟨i, ?_⟩
  intro b hb g hg
  constructor
  · intro n
    obtain ⟨t, x, ht, hNear, hLower⟩ := (hEvery b hb).1 n
    exact ⟨t, ht, hNear,
      lt_of_lt_of_le hLower
        (h3NativeActualVorticityComponentAt_le_vorticityEnvelope
          (hg t ht) i x)⟩
  · intro M
    obtain ⟨t, x, ht, hLower⟩ := (hEvery b hb).2 M
    exact ⟨t, ht,
      lt_of_lt_of_le hLower
        (h3NativeActualVorticityComponentAt_le_vorticityEnvelope
          (hg t ht) i x)⟩

/-- Under the stated raw dissipation ceiling, hypothetical
nonextension makes every vorticity envelope unbounded on each strict
terminal subtail, with near-terminal indexed lower values. -/
theorem positiveGrowth_everyVorticityEnvelope_endpointEscape_of_rawCeiling
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    H3TerminalEveryVorticityEnvelopeEndpointEscape u a T := by
  exact everyVorticityEnvelope_endpointEscape_of_fixedActualVorticity
    (positiveGrowth_fixedActualVorticity_endpointEscape_of_rawCeiling
      hH3 hNoExtension hClass hb₀ hRawCeiling)

/-- Neutral continuation or pointwise endpoint escape in every
admissible vorticity envelope under the stated raw ceiling. -/
theorem smoothContinuationExtension_or_everyVorticityEnvelope_endpointEscape
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a b₀ : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hb₀ : b₀ ∈ Set.Ioo a T)
    (hRawCeiling : H3TerminalNativeUniformRawSubexponentialCeiling u b₀ T) :
    (∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
      SmoothContinuationExtension u v T) ∨
    H3TerminalEveryVorticityEnvelopeEndpointEscape u a T := by
  rcases
      smoothContinuationExtension_or_fixedActualVorticity_endpointEscape
        hH3 hClass hb₀ hRawCeiling with hExtension | hEscape
  · exact Or.inl hExtension
  · exact Or.inr
      (everyVorticityEnvelope_endpointEscape_of_fixedActualVorticity hEscape)

end

end Euclidean
end Bridge
end PrimeTensor
