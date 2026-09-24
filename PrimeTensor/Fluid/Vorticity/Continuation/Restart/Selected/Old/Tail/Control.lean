import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Energy.Class
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Late.Restart

/-!
# Build the late old energy class directly from terminal H³ control

The previous high-order transfer showed that one retained canonical H³ tail
whose remaining lifetime lies inside a single unit-viscosity restart radius
produces an actual `PreterminalH3EnergyClass` on a later midpoint tail.

`TerminalTailH3Control` already contains enough information to manufacture
exactly such a restart.  Its uniform H³ coordinate bound gives one canonical
energy ceiling `E`; positivity of the spectral restart radius then lets us
choose a restart time arbitrarily close to the old terminal time `T`.

Consequently the old smoothing interface

    H3SeedProducesEnergyClass

is not needed after terminal H³ control has already been established.

This file proves two reductions:

1. `TerminalTailH3Control` directly produces a late
   `PreterminalH3EnergyClass`;
2. the existing late-energy-restart package therefore requires only
   `EnergyClassProducesCanonicalH3Data`, not an additional smoothing
   hypothesis.

No new PDE estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldTailControl
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Uniform terminal-tail H³ control alone produces a high-order old energy class
on some later terminal sub-tail.

The construction chooses a canonical restart sufficiently near `T` that its
positive unit-viscosity restart radius covers the whole remaining lifetime,
then applies the selected-to-old high-order transfer.
-/
theorem h3Preterminal_energyClass_of_terminalTailH3Control
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    ∃ a : ℝ,
      PreterminalH3EnergyClass u a T := by

  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  have hR :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1)
      hE

  let ε : ℝ :=
    min
      ((T - a₀) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - a₀) / 2 := by
    linarith [ha₀.2]

  have hHalfRadius :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - a₀) / 2 := by
    dsimp only [ε]
    exact min_le_left _ _

  have hεRadius :
      ε ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact min_le_right _ _

  let t₀ : ℝ :=
    T - ε

  have ht₀T :
      t₀ < T := by
    dsimp only [t₀]
    linarith

  have ha₀t₀ :
      a₀ ≤ t₀ := by
    dsimp only [t₀]
    linarith [hεTail, ha₀.2]

  have ht₀Pos :
      0 < t₀ :=
    lt_of_lt_of_le ha₀.1 ha₀t₀

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Pos, ht₀T⟩

  have hTail₀ :
      CanonicalH3TailDataFrom u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a₀ T :=
      ⟨
        le_trans ha₀t₀ hs.1,
        hs.2
      ⟩

    have hsBound :
        VelocityH3BoundAt u s M :=
      hBound s hsOld

    exact
      ⟨
        velocityH3IntegrableAt_of_bound hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hCover :
      T - t₀ ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    dsimp only [t₀]
    linarith [hεRadius, hR]

  exact
    h3Preterminal_energyClass_of_canonicalTail_radiusCoversTail
      hNS
      ht₀
      hE
      hTail₀
      hCover

/--
Terminal H³ control plus canonical H³ energy closure provide one sufficiently
late energy-regular restart, without any independent
`H3SeedProducesEnergyClass` hypothesis.
-/
theorem h3PreterminalTailUnitViscosityLateEnergyRestartData_of_tailControl
    (hCanonical : EnergyClassProducesCanonicalH3Data)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyRestartData u T := by

  obtain ⟨a₁, hClass⟩ :=
    h3Preterminal_energyClass_of_terminalTailH3Control
      hNS hControl

  have ha₁ :
      a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hData₁ :
      CanonicalH3EnergyDataOnTail u a₁ T :=
    hCanonical u a₁ T hClass

  rcases hControl with
    ⟨a₀, M, ha₀, hM, hBound⟩

  let E : ℝ :=
    velocityH3CoordinateBudget M

  have hE :
      1 ≤ E := by
    dsimp only [E]
    exact
      one_le_velocityH3CoordinateBudget hM

  have hR :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    h3SpectralPreterminalCanonicalEnergyRestartRadius_pos
      (one_pos : (0 : ℝ) < 1)
      hE

  let b : ℝ :=
    max a₀ a₁

  have hbT :
      b < T := by
    dsimp only [b]
    exact max_lt ha₀.2 ha₁.2

  have ha₀b :
      a₀ ≤ b := by
    dsimp only [b]
    exact le_max_left _ _

  have ha₁b :
      a₁ ≤ b := by
    dsimp only [b]
    exact le_max_right _ _

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith [hbT]

  have hHalfRadius :
      0 < h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
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
      ε ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
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
    linarith [hεTail, hbT]

  have ht₀Pos :
      0 < t₀ :=
    lt_of_lt_of_le
      ha₀.1
      (le_trans ha₀b hb₀)

  have ht₀ :
      t₀ ∈ Set.Ioo (0 : ℝ) T :=
    ⟨ht₀Pos, ht₀T⟩

  have hTail₀ :
      CanonicalH3TailDataFrom u t₀ T E := by
    intro s hs

    have hsOld :
        s ∈ Set.Ico a₀ T :=
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
        velocityH3IntegrableAt_of_bound hsBound,
        by
          dsimp only [E]
          exact
            velocityH3EnergyAt_le_coordinateBudget_of_bound
              hsBound
      ⟩

  have hData₀ :
      CanonicalH3EnergyDataOnTail u t₀ T :=
    canonicalH3EnergyDataOnTail_mono_start
      (le_trans ha₁b hb₀)
      ht₀T
      hData₁

  have hCross :
      T - t₀ < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hεLtRadius :
        ε < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have hHalfLt :
          h3FinHeatLerayRestartRadius (1 : ℝ) E / 2
            < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
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
