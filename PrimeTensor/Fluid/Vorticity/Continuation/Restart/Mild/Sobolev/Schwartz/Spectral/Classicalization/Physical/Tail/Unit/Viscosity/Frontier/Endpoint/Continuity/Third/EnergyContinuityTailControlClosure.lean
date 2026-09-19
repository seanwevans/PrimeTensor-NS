import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.HighOrder.Old.TailControl
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyContinuityMinimal

/-!
# Minimal energy continuity directly from terminal H³ control

`EnergyContinuityMinimal` already reduced the pressure-free endpoint argument to
one scalar property:

    CanonicalH3EnergyContinuousOnTail.

Its remaining use of `H3SeedProducesEnergyClass` was only to obtain a late
high-order energy class from terminal H³ control.

`Selected.HighOrder.Old.TailControl` now proves exactly that construction
directly.  Therefore the direct pressure-free continuation route requires only

    EnergyClassProducesCanonicalH3EnergyContinuity.

The stronger `EnergyClassProducesCanonicalH3Data` interface is not needed by
the continuation topology.

No new PDE estimate is introduced in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EnergyContinuityTailControlClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Terminal H³ control plus minimal scalar canonical-energy continuity on every
energy-class tail produces one sufficiently late restart carrying exactly the
data needed by the pressure-free endpoint argument.
-/
theorem h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_tailControl
    (hEnergyCont :
      EnergyClassProducesCanonicalH3EnergyContinuity)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hControl : TerminalTailH3Control u T) :
    H3PreterminalTailUnitViscosityLateEnergyContinuousRestartData
      u T := by

  obtain
    ⟨
      a₁,
      hClass
    ⟩ :=
    h3Preterminal_energyClass_of_terminalTailH3Control
      hNS
      hControl

  have ha₁ :
      a₁ ∈ Set.Ioo (0 : ℝ) T :=
    hClass.terminal_start

  have hCont₁ :
      CanonicalH3EnergyContinuousOnTail
        u a₁ T :=
    hEnergyCont
      u a₁ T hClass

  rcases hControl with
    ⟨
      a₀,
      M,
      ha₀,
      hM,
      hBound
    ⟩

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
    exact
      le_max_left _ _

  have ha₁b :
      a₁ ≤ b := by
    dsimp only [b]
    exact
      le_max_right _ _

  let ε : ℝ :=
    min
      ((T - b) / 2)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E / 2)

  have hHalfTail :
      0 < (T - b) / 2 := by
    linarith [hbT]

  have hHalfRadius :
      0 <
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    linarith

  have hε :
      0 < ε := by
    dsimp only [ε]
    exact
      lt_min hHalfTail hHalfRadius

  have hεTail :
      ε ≤ (T - b) / 2 := by
    dsimp only [ε]
    exact
      min_le_left _ _

  have hεRadius :
      ε ≤
        h3FinHeatLerayRestartRadius (1 : ℝ) E / 2 := by
    dsimp only [ε]
    exact
      min_le_right _ _

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

  have hCont₀ :
      CanonicalH3EnergyContinuousOnTail
        u t₀ T :=
    canonicalH3EnergyContinuousOnTail_mono_start
      (le_trans ha₁b hb₀)
      ht₀T
      hCont₁

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

      exact
        lt_of_le_of_lt hεRadius hHalfLt

    dsimp only [t₀]
    linarith

  exact
    ⟨
      E,
      t₀,
      hE,
      ht₀,
      hTail₀,
      hCont₀,
      hCross
    ⟩

/--
Terminal H³ control produces a complete pressure-free real restart from minimal
canonical H³ energy continuity alone.
-/
theorem h3ControlProducesRealRestart_of_unitViscosityEnergyContinuity
    (hEnergyCont :
      EnergyClassProducesCanonicalH3EnergyContinuity) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain
    ⟨
      E,
      t,
      hE,
      ht,
      hTail,
      hCont,
      hCross
    ⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyContinuousRestartData_of_tailControl
      hEnergyCont
      hNS
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_energyContinuity_pressureFree
      hNS
      ht
      hE
      hTail
      hCont

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ)
        E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS
      ht
      hE
      hTail
      hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS
      ht
      hE
      hTail
      hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS
      ht
      hE
      hTail
      hEvolution
      hCross
      hLocalPDE

/--
Minimal pressure-free continuation closure after terminal H³ control.

The continuation half now consumes only scalar canonical H³ energy continuity
on high-order energy-class tails.
-/
theorem h3ControlProducesExtension_of_unitViscosityEnergyContinuity
    (hEnergyCont :
      EnergyClassProducesCanonicalH3EnergyContinuity) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscosityEnergyContinuity
        hEnergyCont)

/--
Compatibility corollary from the stronger canonical H³ data interface.
-/
theorem h3ControlProducesExtension_of_unitViscosityCanonicalEnergy_via_continuity
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityEnergyContinuity
      (energyClassProducesCanonicalH3EnergyContinuity_of_canonicalData
        hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
