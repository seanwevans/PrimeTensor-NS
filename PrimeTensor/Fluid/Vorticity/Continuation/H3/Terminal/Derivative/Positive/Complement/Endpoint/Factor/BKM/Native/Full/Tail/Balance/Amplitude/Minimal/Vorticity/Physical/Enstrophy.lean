import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Full.Tail.Balance.Amplitude.Minimal.Vorticity.Physical.Fixed.Orientation
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Terminal.Derivative.Positive.Complement.Endpoint.Factor.BKM.Native.Selected.Enstrophy.Rate

/-!
# Pure physical pointwise-enstrophy escape

The pure physical minimal-vorticity sequence already carries one fixed actual
vorticity component with one fixed one-sided orientation.  Shifting that
sequence by three indices removes the harmless low-index offset in the linear
component bound.  The square of the oriented component is the square of the
actual component, and every actual component square is bounded by pointwise
real enstrophy.

Thus hypothetical nonextension produces a purely physical terminal sequence
on which

    n^2 < realEnstrophyDensity

at the selected spacetime points, while the shrinking terminal localization,
minimal-envelope escape, fixed component, and fixed orientation are retained.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

private theorem tendsto_atTop_of_natSquare_lt_physicalEnstrophy
    {f : ℕ → ℝ}
    (hf : ∀ n : ℕ, (n : ℝ) ^ 2 < f n) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro C

  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max C 1)

  filter_upwards [eventually_ge_atTop N] with n hn

  have hCN : C < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left C 1) hN

  have hOneN : 1 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right C 1) hN

  have hCast : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hOne : 1 ≤ (n : ℝ) := by
    linarith

  have hLinearSquare :
      (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]

  exact
    le_of_lt
      (lt_trans
        (lt_of_lt_of_le hCN hCast)
        (lt_of_le_of_lt hLinearSquare (hf n)))

/-- Pure physical terminal escape with one fixed oriented actual-vorticity
component and quadratic pointwise-enstrophy growth. -/
def H3TerminalMinimalVorticityPhysicalEnstrophyEscapeSequence
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
            (n : ℝ) <
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
            ∧
          (∀ n : ℕ,
            (n : ℝ) ^ 2 <
              realEnstrophyDensity
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) (z n))
            ∧
          Tendsto
            (fun n : ℕ =>
              realEnstrophyDensity
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                (τ n) (z n))
            atTop atTop

/-- Hypothetical nonextension forces quadratic pointwise real-enstrophy growth
on a purely physical terminal sequence carrying the same fixed oriented actual
vorticity component and minimal-envelope escape. -/
theorem exists_terminal_minimalVorticityPhysicalEnstrophyEscapeSequence_of_noH3PathExtension
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hNoExtension :
      ¬ ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T)
    (hClass : PreterminalH3EnergyClass u a T) :
    H3TerminalMinimalVorticityPhysicalEnstrophyEscapeSequence u T := by
  obtain
    ⟨
      i,
      s,
      σ,
      x,
      hData,
      hSigmaTendsto,
      hEnvelopeTendsto,
      hOrientedLower,
      hOrientedTendsto
    ⟩ :=
    exists_terminal_minimalVorticityPhysicalFixedOrientedComponentEscapeSequence_of_noH3PathExtension
      hH3 hNoExtension hClass

  let k : ℕ → ℕ := fun n => n + 3
  let τ : ℕ → ℝ := fun n => σ (k n)
  let z : ℕ → Point3 := fun n => x (k n)

  have hKTop : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    dsimp only [k]
    omega

  have hReindexedData :
      ∀ n : ℕ,
        τ n ∈
            Set.Ioo
              (T - (1 : ℝ) / ((n : ℝ) + 1))
              T
          ∧
        (n : ℝ) < h3MinimalVorticityEnvelopeAt u (τ n) := by
    intro n

    have hIndexNat : n ≤ k n := by
      dsimp only [k]
      omega

    have hIndex : (n : ℝ) ≤ (k n : ℝ) := by
      exact_mod_cast hIndexNat

    have hDenPos : 0 < (n : ℝ) + 1 := by
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
      exact lt_of_le_of_lt hIndex hOld.2

  have hOrientedLowerShifted :
      ∀ n : ℕ,
        (n : ℝ) <
          h3TerminalOrientedValue
            s
            (h3NativeActualVorticityComponentAt u i (τ n) (z n)) := by
    intro n

    have hOld := hOrientedLower (k n)

    have hCast :
        (k n : ℝ) = (n : ℝ) + 3 := by
      dsimp only [k]
      norm_num

    rw [hCast] at hOld

    dsimp only [τ, z]
    linarith

  have hEnstrophyLower :
      ∀ n : ℕ,
        (n : ℝ) ^ 2 <
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) (z n) := by
    intro n

    let w : ℝ :=
      h3NativeActualVorticityComponentAt u i (τ n) (z n)

    let o : ℝ :=
      h3TerminalOrientedValue s w

    have hOrient : (n : ℝ) < o := by
      simpa only [o, w] using hOrientedLowerShifted n

    have hONonneg : 0 ≤ o := by
      exact le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg n) hOrient)

    have hSquare :
        (n : ℝ) ^ 2 < o ^ 2 :=
      (sq_lt_sq₀ (Nat.cast_nonneg n) hONonneg).2 hOrient

    have hOrientSquare : o ^ 2 = w ^ 2 := by
      dsimp only [o]
      cases s <;> simp [h3TerminalOrientedValue]

    have hComponentSquare :
        w ^ 2 ≤
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) (z n) := by
      dsimp only [w]
      exact
        native_actualVorticityComponent_sq_le_realEnstrophy
          u i (τ n) (z n)

    exact
      hSquare.trans_le
        (hOrientSquare.le.trans hComponentSquare)

  have hEnstrophyTendsto :
      Tendsto
        (fun n : ℕ =>
          realEnstrophyDensity
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            (τ n) (z n))
        atTop atTop :=
    tendsto_atTop_of_natSquare_lt_physicalEnstrophy hEnstrophyLower

  exact
    ⟨
      i,
      s,
      τ,
      z,
      hReindexedData,
      hSigmaTendsto.comp hKTop,
      hEnvelopeTendsto.comp hKTop,
      hOrientedLowerShifted,
      hOrientedTendsto.comp hKTop,
      hEnstrophyLower,
      hEnstrophyTendsto
    ⟩

/-- Neutral formulation: either the H³ path continues smoothly, or a purely
physical terminal sequence carries fixed one-sided actual-vorticity escape and
quadratic pointwise-enstrophy growth. -/
theorem smoothContinuationExtension_or_terminal_minimalVorticityPhysicalEnstrophyEscapeSequence
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T) :
    (
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
    )
      ∨
    H3TerminalMinimalVorticityPhysicalEnstrophyEscapeSequence u T := by
  classical
  by_cases hExtension :
      ∃ v : SpaceTimeVectorField ℝ ℝ MulReal Depth.three,
        SmoothContinuationExtension u v T
  · exact Or.inl hExtension
  · exact
      Or.inr
        (exists_terminal_minimalVorticityPhysicalEnstrophyEscapeSequence_of_noH3PathExtension
          hH3 hExtension hClass)

end

end Euclidean
end Bridge
end PrimeTensor
