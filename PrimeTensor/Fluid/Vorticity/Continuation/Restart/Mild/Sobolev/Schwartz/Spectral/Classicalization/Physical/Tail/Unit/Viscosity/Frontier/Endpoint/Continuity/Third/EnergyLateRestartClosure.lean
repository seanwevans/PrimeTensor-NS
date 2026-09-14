import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyLateRestart
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Mixed.Closed.PDE.Closure

/-!
# Late energy-regular restart: direct continuation closure

The previous increment selected one restart time `t` which simultaneously has

* retained canonical H³ tail data;
* canonical high-order H³ energy data;
* enough explicit spectral lifespan to cross the old terminal time.

The older continuation reductions were phrased globally over every possible
restart time.  That is stronger than the actual continuation construction
needs.  This file closes the one-anchor route directly.

There are two steps.

1. **Local PDE closure.**
   At one anchor, one physical-tail evolution witness already supplies every
   remaining local PDE field.  The selected restart has closed temporal and
   mixed derivative regularity; the canonical selected pressure has spatial
   `C²`; momentum and incompressibility are already proved.  Reassembling these
   gives `H3PreterminalTailUnitViscosityLocalPDEAt`.

2. **Late restart closure.**
   The global old-pressure frontier gives zeroth physical `L²` continuity at
   the selected late anchor.  Canonical H³ energy data gives scalar energy
   continuity there, which together with the already-closed weak H³ argument
   gives ordered-third physical `L²` continuity.  The two halves give
   radius-wide endpoint continuity, hence physical-tail evolution.  The local
   PDE closure then produces a complete real restart across `T`.

Consequently the continuation theorem no longer needs global third-order
continuity or global physical-tail evolution.  Its remaining analytic inputs
are aligned with existing project interfaces:

* old preterminal pressure-gradient mass;
* smoothing into `PreterminalH3EnergyClass`;
* production of canonical H³ energy data from that class.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityLateRestartDirectClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At one retained canonical H³ tail, physical-tail evolution already closes
the normalized local PDE witness.  This is the local form hidden inside the
previous global selected-PDE closure. -/
theorem h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityLocalPDEAt
      hNS ht hE hTail := by
  intro hCross

  let R : ℝ :=
    h3FinHeatLerayRestartRadius (1 : ℝ) E

  let S : ℝ :=
    (T + (t + R)) / 2

  have hTUpper :
      T < t + R := by
    have h :=
      (sub_lt_iff_lt_add).1 hCross
    simpa only [R, add_comm] using h

  have hTS :
      T < S := by
    dsimp only [S]
    linarith

  have hSR :
      S - t < R := by
    dsimp only [S]
    linarith

  have hSR' :
      S - t <
        h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    simpa only [R] using hSR

  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedPressureLocalFill
      hNS ht hE hTail

  have hPressure :
      H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
        p S := by
    dsimp only [p]
    exact
      h3PreterminalTailCanonicalSelectedPressureLocalFill_pressureSpatialRegularity
        hNS ht hE hTail hTS hSR'

  have hMomentum :
      H3PreterminalTailUnitViscosityMomentumAt
        hNS ht hE hTail p S := by
    dsimp only [p]
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_pressureMomentum
        hNS ht hE hTail hEvolution hTS hSR'

  have hMixed :
      H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
        hNS ht hE hTail S :=
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_closed
      hNS ht hE hTail hEvolution hTS hSR'

  have hSelectedDerivative :
      H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt
        hNS ht hE hTail p S :=
    h3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt_of_closedTemporal
      hNS ht hE hTail
      p
      hPressure
      hMixed
      hMomentum

  have hSelectedTemporal :
      H3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt
        hNS ht hE hTail p S :=
    h3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt_of_selectedDerivative
      hNS ht hE hTail
      p
      hSelectedDerivative

  have hLocalRemainder :
      H3PreterminalTailUnitViscosityLocalPDERemainderAt
        hNS ht hE hTail p S :=
    h3PreterminalTailUnitViscosityLocalPDERemainderAt_of_selectedTemporal
      hNS ht hE hTail
      hEvolution
      hTS
      hSR'
      p
      hSelectedTemporal

  have hComponents :
      H3PreterminalTailUnitViscosityLocalPDEComponentsAt
        hNS ht hE hTail p S :=
    h3PreterminalTailUnitViscosityLocalPDEComponentsAt_of_remainder
      hNS ht hE hTail
      hSR'
      p
      hLocalRemainder

  have hPDE :
      PreterminalNavierStokes3
        (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
          hNS ht hE hTail S)
        p
        S :=
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_preterminalNavierStokes3_of_components
      hNS ht hE hTail
      hEvolution
      hTS
      hSR'
      p
      hComponents

  exact
    ⟨
      p,
      S,
      hTS,
      hSR',
      hPDE
    ⟩

/-- Canonical H³ energy data plus the old-pressure frontier close the
radius-wide endpoint continuity requirement at one fixed retained tail. -/
theorem h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_oldPressure_of_canonicalEnergyData
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hData :
      CanonicalH3EnergyDataOnTail u t T) :
    H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  have hZeroGlobal :
      H3PreterminalTailUnitViscosityZeroContinuityFrontier :=
    h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_oldPressure
      hOld

  have hZero :
      H3PreterminalTailUnitViscosityZeroContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hZeroGlobal E hE u T t hNS ht hTail

  have hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail := by
    intro q hqPos hEnd

    have hOldLocal :
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
          hNS ht hEnd hTail :=
      hOld E hE u T t hNS ht hTail q hqPos hEnd

    have hPhysicalEnergy :
        H3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed
          hNS ht hEnd hTail :=
      h3PreterminalCanonicalPhysicalH3EnergyContinuousOnElapsed_of_canonicalH3EnergyData
        hNS ht hqPos hEnd hTail hData

    have hSquareEnergy :
        H3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed
          hNS ht hEnd hTail :=
      h3PreterminalCanonicalSpectralSquareEnergyContinuousOnElapsed_of_physicalEnergy
        hNS ht hEnd hTail hPhysicalEnergy

    have hSpectral :
        H3PreterminalCanonicalSpectralStateContinuousOnElapsed
          hNS ht hEnd hTail :=
      h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_oldPressure_of_squareEnergy
        hNS ht hqPos hEnd hE hTail
        hOldLocal
        hSquareEnergy

    exact
      h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_spectralState
        hNS ht hEnd hTail hSpectral

  exact
    h3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius_of_zero_third
      hNS ht hE hTail
      hZero
      hThird

/-- The late energy-regular restart selected from terminal H³ control closes a
complete real restart across `T`.

No global third-continuity or physical-evolution frontier is used: everything
is instantiated only at the selected late anchor. -/
theorem h3ControlProducesRealRestart_of_unitViscosityZeroOldPressureSmoothingCanonicalEnergy
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesRealRestart := by
  intro u T hNS hControl

  obtain
    ⟨
      E,
      t,
      hE,
      ht,
      hTail,
      hData,
      hCross
    ⟩ :=
    h3PreterminalTailUnitViscosityLateEnergyRestartData_of_smoothing
      hSmooth
      hCanonical
      hNS
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_oldPressure_of_canonicalEnergyData
      hOld
      hNS ht hE hTail hData

  have hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail :=
    h3PreterminalTailPhysicalEvolutionOnRestartRadius_of_unitViscosity_endpointContinuity
      hNS ht hE hTail hEndpoint

  have hLocalPDE :
      H3PreterminalTailUnitViscosityLocalPDEAt
        hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityLocalPDEAt_closed_of_evolution
      hNS ht hE hTail hEvolution

  exact
    h3PreterminalTailUnitViscosityRealRestartAt_of_localPDE
      hNS ht hE hTail
      hEvolution
      hCross
      hLocalPDE

/-- Final direct continuation reduction at the current stage.

The formerly global ordered-third continuity frontier has disappeared.  The
remaining independent analytic obligations are exactly the already-named
old-pressure, smoothing, and canonical-H³-energy interfaces. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureSmoothingCanonicalEnergy
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscosityZeroOldPressureSmoothingCanonicalEnergy
        hOld hSmooth hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
