import PrimeTensor.Fluid.Vorticity.Continuation.Landau
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyLateRestartClosure

/-!
# Landau continuation through the direct late H³ restart

The Landau/BKM energy route and the explicit restart route share the same
high-order structural inputs:

* `H3SeedProducesEnergyClass`;
* `EnergyClassProducesCanonicalH3Data`.

The transport side now asks only for `EnergyClassProducesGradientEnvelope`;
top-order whole-space flux cancellation is derived downstream from those data.

Previously the Landau-facing continuation theorem still accepted an abstract
`H3ControlProducesExtension` (or a separate local-well-posedness/lifespan
frontier).  `EnergyLateRestartClosure` removes that duplication.

Given terminal H³ control, the same smoothing and canonical-energy hypotheses
already used on the BKM side select one sufficiently late energy-regular
restart.  The explicit spectral restart construction then crosses the terminal
time once the zeroth-order old-pressure mass frontier is supplied.

Thus the seeded Landau continuation criterion now has a single
continuation-specific analytic input:

    H3PreterminalTailUnitViscosityZeroOldPressureFrontier.

No independent uniform lifespan, abstract continuation theorem, global
third-order continuity frontier, or global physical-tail evolution frontier
remains in this statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Direct Landau/BKM continuation through the explicit late energy-regular
restart.

The smoothing and canonical-energy assumptions are shared by both halves:
they first yield terminal H³ control from the vorticity criterion and then
supply the energy-regular late restart used by the continuation construction.
The only additional continuation-specific hypothesis is the old preterminal
pressure-gradient mass frontier. -/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure_zeroOldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hGradient :
      EnergyClassProducesGradientEnvelope)
    (hEndpoint :
      VorticityControlsGradientLogarithmically) :
    SeededVorticityL1LinfProducesExtension := by
  apply
    seededVorticityL1LinfProducesExtension_of_landauClosure
      hSmooth
      hCanonical
      hGradient
      hEndpoint

  exact
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSmoothingCanonicalEnergy
      hOld
      hSmooth
      hCanonical

/-- Factorized form making the shared assumptions explicit.

Under the Landau-side hypotheses, the vorticity criterion gives terminal H³
control; under the same smoothing/canonical-energy pair plus old-pressure
control, terminal H³ control gives a continuation extension. -/
theorem seededVorticityL1LinfProducesExtension_of_landauH3Control_and_directRestart
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hGradient :
      EnergyClassProducesGradientEnvelope)
    (hEndpoint :
      VorticityControlsGradientLogarithmically) :
    SeededVorticityL1LinfProducesExtension := by
  have hLandau :
      EnergyClassProducesLandauTransportAnalytic :=
    energyClassProducesLandauTransportAnalytic_of_gradientEnvelope
      hCanonical
      hGradient

  have hH3 :
      VorticityL1LinfProducesH3Control :=
    vorticityL1LinfProducesH3Control_of_landauClosure
      hSmooth
      hCanonical
      hLandau
      hEndpoint

  have hContinue :
      H3ControlProducesExtension :=
    h3ControlProducesExtension_of_unitViscosityZeroOldPressureSmoothingCanonicalEnergy
      hOld
      hSmooth
      hCanonical

  exact
    seededVorticityL1LinfProducesExtension_of_H3Factorization
      hH3
      hContinue

end Euclidean
end Bridge
end PrimeTensor
