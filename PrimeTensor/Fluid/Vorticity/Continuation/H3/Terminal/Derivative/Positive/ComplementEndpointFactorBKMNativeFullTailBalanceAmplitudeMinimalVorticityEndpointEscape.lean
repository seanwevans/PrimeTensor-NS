import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.ComplementEndpointFactorBKMNativeFullTailBalanceAmplitudeMinimalVorticityCeilingContinuation

/-!
# Minimal-vorticity envelope endpoint escape

A bounded minimal common vorticity envelope on any strict terminal tail forces
smooth continuation.  Taking the direct contrapositive gives a clean physical
endpoint obstruction under hypothetical nonextension: every strict terminal tail
contains points where the minimal envelope exceeds every prescribed finite
threshold.

This statement is deliberately phrased without selecting a special sequence or
native witness.  It is the cofinal physical-time form of the terminal vorticity
criterion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

/-- The minimal common vorticity envelope exceeds every finite threshold on
every strict terminal tail. -/
def H3TerminalMinimalVorticityEnvelopeCofinallyUnbounded
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ) : Prop :=
  ∀ b : ℝ,
    b ∈ Set.Ioo a T →
      ∀ M : ℝ,
        ∃ t : ℝ,
          t ∈ Set.Ioo b T
            ∧
          M < h3MinimalVorticityEnvelopeAt u t

/-- Hypothetical nonextension forces cofinal physical-time unboundedness of the
minimal common vorticity envelope on every strict terminal tail. -/
theorem h3TerminalMinimalVorticityEnvelope_cofinallyUnbounded_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityEnvelopeCofinallyUnbounded u a T := by
  intro b hb M
  by_contra hNoWitness

  have hCeiling :
      ∀ t : ℝ,
        t ∈ Set.Ioo b T →
          h3MinimalVorticityEnvelopeAt u t ≤ M := by
    intro t ht
    exact le_of_not_gt (by
      intro hGt
      exact hNoWitness ⟨t, ht, hGt⟩)

  have hExtension :=
    smoothContinuationExtension_of_terminal_minimalVorticityEnvelope_ceiling
      hH3 hClass hb hCeiling

  exact hNoExtension hExtension

/-- Neutral endpoint alternative: either the H³ path continues smoothly, or
the minimal common vorticity envelope is cofinally unbounded on every strict
terminal tail. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityEnvelope_cofinallyUnbounded
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityEnvelopeCofinallyUnbounded u a T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact Or.inr
      (h3TerminalMinimalVorticityEnvelope_cofinallyUnbounded_of_noH3PathExtension
        hH3 hExtension hClass)

/-- Midpoint-tail specialization: under nonextension, the minimal envelope is
unbounded on the canonical strict midpoint tail. -/
theorem exists_midpoint_tail_minimalVorticityEnvelope_gt_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a M : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    ∃ t : ℝ,
      t ∈ Set.Ioo (h3BKMKineticTailMidpoint a T) T
        ∧
      M < h3MinimalVorticityEnvelopeAt u t := by
  exact
    h3TerminalMinimalVorticityEnvelope_cofinallyUnbounded_of_noH3PathExtension
      hH3 hNoExtension hClass
      (h3BKMKineticTailMidpoint a T)
      (h3BKMKineticTailMidpoint_mem_Ioo hClass.terminal_start.2)
      M

end

end Euclidean
end Bridge
end PrimeTensor
