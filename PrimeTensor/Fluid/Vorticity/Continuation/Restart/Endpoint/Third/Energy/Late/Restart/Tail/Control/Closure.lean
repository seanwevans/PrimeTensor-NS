import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.Tail.Control
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Late.Restart.Pressure.Free.Closure

/-!
# Pressure-free late restart directly from terminal H³ control

`Selected.HighOrder.Old.TailControl` removes the independent smoothing
hypothesis from the late-energy-restart package:

    TerminalTailH3Control
      -> late PreterminalH3EnergyClass
      -> H3PreterminalTailUnitViscosityLateEnergyRestartData

once `EnergyClassProducesCanonicalH3Data` is supplied.

The pressure-free endpoint closure already showed that canonical H³ energy data
at the selected anchor is enough to recover radius-wide endpoint continuity,
physical-tail evolution, the local PDE witness, and finally a real restart
across the old terminal time.

Combining those two facts removes

    H3SeedProducesEnergyClass

from the continuation half altogether.  The only remaining energy-side
interface in the direct pressure-free `H3ControlProducesExtension` route is

    EnergyClassProducesCanonicalH3Data.

No new analytic estimate is introduced here; this file is the minimal
factorization obtained from the two previously proved closures.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityLateRestartTailControlClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/--
Terminal H³ control produces a complete pressure-free real restart from the
canonical H³ energy-data closure alone.

The high-order energy class needed to invoke `hCanonical` is now manufactured
internally from `hControl`.
-/
theorem h3ControlProducesRealRestart_of_unitViscosityCanonicalEnergy
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
    h3PreterminalTailUnitViscosityLateEnergyRestartData_of_tailControl
      hCanonical
      hNS
      hControl

  have hEndpoint :
      H3PreterminalTailUnitViscosityEndpointContinuityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    h3PreterminalTailUnitViscosityEndpointContinuityOnRestartRadius_of_canonicalEnergyData_pressureFree
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

/--
Pressure-free direct continuation from terminal H³ control now requires only
canonical H³ energy-data closure.

In particular, `H3SeedProducesEnergyClass` is no longer an assumption of the
continuation half of the BKM/Landau factorization.
-/
theorem h3ControlProducesExtension_of_unitViscosityCanonicalEnergy
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscosityCanonicalEnergy
        hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
