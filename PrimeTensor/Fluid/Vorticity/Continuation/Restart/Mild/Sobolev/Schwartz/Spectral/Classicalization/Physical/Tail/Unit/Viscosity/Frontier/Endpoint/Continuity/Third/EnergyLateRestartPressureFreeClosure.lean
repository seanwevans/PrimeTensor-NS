import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EndpointPressureFreeEnergy
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyLateRestartClosure

/-!
# Pressure-free late energy-regular restart closure

`EndpointPressureFreeEnergy` removes the last use of the old-pressure frontier
from endpoint topology.  At the selected late restart anchor, canonical H³
energy data alone now gives the complete radius-wide endpoint-continuity
frontier.

The rest of the direct late-restart construction was already pressure-free:

* endpoint continuity gives physical-tail evolution;
* physical-tail evolution closes the local PDE witness;
* the crossing inequality then produces a real restart beyond `T`.

Therefore the direct continuation theorem now requires only the two
energy-side interfaces

    H3SeedProducesEnergyClass
    EnergyClassProducesCanonicalH3Data.

No old-pressure frontier appears in either theorem below.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityLateRestartPressureFreeClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected late energy-regular anchor produces a complete real restart
without any old-pressure hypothesis. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingCanonicalEnergy
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

/-- Pressure-free direct continuation closure.

Terminal H³ control produces an extension once the existing smoothing and
canonical-energy interfaces are supplied; no independent old-pressure
hypothesis remains. -/
theorem h3ControlProducesExtension_of_unitViscositySmoothingCanonicalEnergy
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_realRestart
      (h3ControlProducesRealRestart_of_unitViscositySmoothingCanonicalEnergy
        hSmooth hCanonical)

end

end Euclidean
end Bridge
end PrimeTensor
