import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Fixed.Component
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Fixed.Curl.Gradient.Orientation
import Mathlib.Order.Filter.Finite

/-!
# Fixed one-sided actual-vorticity escape on the pure physical sequence

The pure physical minimal-vorticity sequence already freezes one actual
vorticity component while preserving shrinking terminal localization and
minimal-envelope escape.  Its sign may still vary.

Orient each real component value toward its sign.  The resulting orientation
lies in a two-element finite space, so one orientation occurs frequently and a
strictly increasing extraction freezes it.  The physical localization,
minimal-envelope lower rate, and component lower rate all survive the
extraction.  Thus one fixed physical vorticity component has a fixed one-sided
escape on a purely physical terminal sequence.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private def h3PhysicalVorticityOrientationOfReal
    (z : ℝ) : H3TerminalOrientation :=
  if 0 ≤ z then
    H3TerminalOrientation.positive
  else
    H3TerminalOrientation.negative

private theorem h3TerminalOrientedValue_physicalVorticityOrientation_eq_abs
    (z : ℝ) :
    h3TerminalOrientedValue
        (h3PhysicalVorticityOrientationOfReal z)
        z
      =
    |z| := by
  by_cases hz : 0 ≤ z
  · simp [h3PhysicalVorticityOrientationOfReal, hz, abs_of_nonneg hz]
  · have hzNeg : z < 0 := lt_of_not_ge hz
    simp [h3PhysicalVorticityOrientationOfReal, hz, abs_of_neg hzNeg]

local instance h3TerminalOrientationFintypePhysicalVorticity :
    Fintype H3TerminalOrientation where
  elems :=
    {
      H3TerminalOrientation.positive,
      H3TerminalOrientation.negative
    }
  complete s := by
    cases s <;> simp

/-- Pure physical-time terminal escape with one fixed actual vorticity
component and one fixed one-sided orientation. -/
def H3TerminalMinimalVorticityPhysicalFixedOrientedComponentEscapeSequence
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃ i : Fin 3,
    ∃ s : H3TerminalOrientation,
      ∃ τ : ℕ → ℝ,
        ∃ z : ℕ → Point3,
          (∀ n : ℕ,
            τ n ∈
                Set.Ioo
                  (T - (1 : ℝ) / ((n : ℝ) + 1))
                  T
              ∧
            (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ n))
            ∧
          Tendsto τ atTop (𝓝 T)
            ∧
          Tendsto
            (fun n : ℕ => h3MinimalVorticityEnvelopeAt u (τ n))
            atTop atTop
            ∧
          (∀ n : ℕ,
            (n : ℝ) - 2 <
              h3TerminalOrientedValue
                s
                (h3NativeActualVorticityComponentAt u i (τ n) (z n)))
            ∧
          Tendsto
            (fun n : ℕ =>
              h3TerminalOrientedValue
                s
                (h3NativeActualVorticityComponentAt u i (τ n) (z n)))
            atTop atTop

/-- Hypothetical nonextension produces a purely physical terminal sequence on
which the minimal envelope and one fixed, one-sided actual vorticity component
both diverge. -/
theorem exists_terminal_minimalVorticityPhysicalFixedOrientedComponentEscapeSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityPhysicalFixedOrientedComponentEscapeSequence
      u T := by
  obtain
    ⟨
      i,
      σ,
      x,
      hData,
      hSigmaTendsto,
      hEnvelopeTendsto,
      hAbsLower,
      hAbsTendsto
    ⟩ :=
    exists_terminal_minimalVorticityPhysicalFixedComponentEscapeSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  let orientation : ℕ → H3TerminalOrientation :=
    fun n =>
      h3PhysicalVorticityOrientationOfReal
        (h3NativeActualVorticityComponentAt u i (σ n) (x n))

  have hFrequentlySomeOrientation :
      ∃ᶠ n : ℕ in atTop,
        ∃ q : H3TerminalOrientation,
          orientation n = q :=
    Frequently.of_forall
      (fun n => ⟨orientation n, rfl⟩)

  obtain ⟨s, hOrientationFrequently⟩ :=
    (Filter.frequently_exists).1 hFrequentlySomeOrientation

  obtain ⟨k, hKMono, hOrientationFixed⟩ :=
    extraction_of_frequently_atTop hOrientationFrequently

  have hKTop : Tendsto k atTop atTop :=
    hKMono.tendsto_atTop

  let τ : ℕ → ℝ := fun n => σ (k n)
  let z : ℕ → Point3 := fun n => x (k n)

  have hFixedSign :
      ∀ n : ℕ,
        h3PhysicalVorticityOrientationOfReal
            (h3NativeActualVorticityComponentAt
              u i (σ (k n)) (x (k n)))
          = s := by
    intro n
    simpa only [orientation] using hOrientationFixed n

  have hReindexedData :
      ∀ n : ℕ,
        τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
          ∧
        (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ n) := by
    intro n

    have hIndexLeNat : n ≤ k n :=
      hKMono.le_apply

    have hIndexLe :
        (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hIndexLeNat

    have hDenPos :
        0 < (n : ℝ) + 1 := by
      positivity

    have hInv :
        (1 : ℝ) / ((k n : ℝ) + 1)
          ≤
        1 / ((n : ℝ) + 1) := by
      exact
        one_div_le_one_div_of_le
          hDenPos
          (by linarith)

    have hOld := hData (k n)

    constructor
    · constructor
      · dsimp only [τ]
        linarith [(hOld.1).1, hInv]
      · dsimp only [τ]
        exact (hOld.1).2
    · dsimp only [τ]
      exact lt_of_le_of_lt hIndexLe hOld.2

  have hOrientedLower :
      ∀ n : ℕ,
        (n : ℝ) - 2 <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt u i (τ n) (z n)) := by
    intro n

    have hIndexLeNat : n ≤ k n :=
      hKMono.le_apply

    have hIndexLe :
        (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hIndexLeNat

    have hOld := hAbsLower (k n)

    have hEq :
        h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (σ (k n)) (x (k n)))
          =
        |h3NativeActualVorticityComponentAt
            u i (σ (k n)) (x (k n))| := by
      rw [← hFixedSign n]
      exact
        h3TerminalOrientedValue_physicalVorticityOrientation_eq_abs
          (h3NativeActualVorticityComponentAt
            u i (σ (k n)) (x (k n)))

    dsimp only [τ, z]
    rw [hEq]
    linarith

  have hOrientedTendsto :
      Tendsto
        (fun n : ℕ =>
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt u i (τ n) (z n)))
        atTop atTop := by
    have hAbsSub :
        Tendsto
          (fun n : ℕ =>
            |h3NativeActualVorticityComponentAt
              u i (σ (k n)) (x (k n))|)
          atTop atTop := by
      change
        Tendsto
          ((fun n : ℕ =>
              |h3NativeActualVorticityComponentAt u i (σ n) (x n)|) ∘ k)
          atTop atTop
      exact hAbsTendsto.comp hKTop

    have hEqFun :
        (fun n : ℕ =>
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt
              u i (σ (k n)) (x (k n))))
          =
        (fun n : ℕ =>
          |h3NativeActualVorticityComponentAt
            u i (σ (k n)) (x (k n))|) := by
      funext n
      rw [← hFixedSign n]
      exact
        h3TerminalOrientedValue_physicalVorticityOrientation_eq_abs
          (h3NativeActualVorticityComponentAt
            u i (σ (k n)) (x (k n)))

    dsimp only [τ, z]
    rw [hEqFun]
    exact hAbsSub

  exact
    ⟨
      i,
      s,
      τ,
      z,
      hReindexedData,
      hSigmaTendsto.comp hKTop,
      hEnvelopeTendsto.comp hKTop,
      hOrientedLower,
      hOrientedTendsto
    ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or one fixed
actual vorticity component has one fixed one-sided escape on a purely physical
terminal sequence that also carries minimal-envelope escape. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityPhysicalFixedOrientedComponentEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityPhysicalFixedOrientedComponentEscapeSequence
      u T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_minimalVorticityPhysicalFixedOrientedComponentEscapeSequence_of_noH3PathExtension
          hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
