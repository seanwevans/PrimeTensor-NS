import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Tail.Restriction

/-!
# Ordered-third endpoint continuity: select one late energy-regular restart

The global endpoint frontiers quantify over every retained restart time.  The
actual continuation argument does not need that strength: it is free to choose
one restart time sufficiently close to the candidate terminal time.

This file packages that selection.

Assume:

* `TerminalTailH3Control u T`, beginning at some old H³-tail start `a₀`;
* `H3SeedProducesEnergyClass`, producing a high-order energy-class start `a₁`;
* `EnergyClassProducesCanonicalH3Data`, producing canonical H³ energy data on
  `[a₁,T)`.

Let

    b = max a₀ a₁.

Both starts lie strictly before `T`, so `b < T`.  For the canonical energy
ceiling obtained from the old H³ bound, let `R` be the unit-viscosity spectral
restart radius.  Choose

    ε = min ((T-b)/2) (R/2),
    t₀ = T - ε.

Then:

* `b ≤ t₀ < T`;
* the old H³ tail restricts to `CanonicalH3TailDataFrom u t₀ T E`;
* the canonical H³ energy package restricts to `CanonicalH3EnergyDataOnTail
  u t₀ T`;
* `T - t₀ < R`.

Thus the high-order energy class only has to exist somewhere on the terminal
tail; the restart can be selected after it has begun.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityThirdEnergyLateRestart
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One late restart carrying both the retained canonical H³ tail and the
canonical high-order energy data, with enough spectral lifespan to cross the
old terminal time. -/
def H3PreterminalTailUnitViscosityLateEnergyRestartData
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ) : Prop :=
  ∃
    (E t : ℝ),
      1 ≤ E
        ∧
      t ∈ Set.Ioo (0 : ℝ) T
        ∧
      CanonicalH3TailDataFrom u t T E
        ∧
      CanonicalH3EnergyDataOnTail u t T
        ∧
      T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E

/-- Terminal H³ control plus the existing smoothing and canonical-energy
closure interfaces always provide one sufficiently late energy-regular restart.
-/
theorem h3PreterminalTailUnitViscosityLateEnergyRestartData_of_smoothing
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS :
      LoggedPreterminalNavierStokesAdmissible u T)
    (hControl :
      TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyRestartData
      u T := by
  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  have hSeed :
      PreterminalH3Seed u T := by
    exact
      ⟨
        a₀,
        M,
        ha₀,
        hM,
        hBound a₀ ⟨le_rfl, ha₀.2⟩
      ⟩

  rcases hSmooth u T hNS hSeed with
    ⟨a₁, hClass⟩

  have ha₁ :
      a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hData₁ :
      CanonicalH3EnergyDataOnTail
        u a₁ T :=
    hCanonical u a₁ T hClass

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  have hR :
      0 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1)
      hE

  let b : ℝ :=
    max a₀ a₁

  have hbT :
      b < T := by
    dsimp only [b]
    exact
      max_lt ha₀.2 ha₁.2

  have ha₀b :
      a₀ ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have ha₁b :
      a₁ ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  have hTb :
      0 < T - b := by
    linarith

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith

  have hHalfRadius :
      0 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - b) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀T :
      t₀ < T := by
    dsimp only [t₀]
    linarith

  have hb₀ :
      b ≤ t₀ := by
    dsimp only [t₀]
    linarith

  have ht₀Pos :
      0 < t₀ := by
    exact
      lt_of_lt_of_le
        ha₀.1
        (le_trans ha₀b hb₀)

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Pos, ht₀T⟩

  have hTail₀ :
      CanonicalH3TailDataFrom
        u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a₀ T := by
      exact
        ⟨
          le_trans
            (le_trans ha₀b hb₀)
            hs.1,
          hs.2
        ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound
          hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hData₀ :
      CanonicalH3EnergyDataOnTail
        u t₀ T := by
    exact
      canonicalH3EnergyDataOnTail_mono_start
        (le_trans ha₁b hb₀)
        ht₀T
        hData₁

  have hCross :
      T - t₀ <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hεLtRadius :
        ε <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius (1 : ℝ) E / 2
            <
          h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        linarith
      exact lt_of_le_of_lt hεRadius hHalfLt

    dsimp only [t₀]
    linarith

  exact
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail₀,
      hData₀,
      hCross
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
