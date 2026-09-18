import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure.Landau.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.TopFlux.TailClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.LocalWellPosedness

/-!
# Landau H³ continuation factorization

The explicit Landau H³ transport closure has already been carried through the
canonical energy estimate, BKM logarithmic endpoint, and scalar Osgood step to

    VorticityL1LinfProducesH3Control.

The abstract tail-H³ continuation implication

    H3ControlProducesExtension

is still available as a factorized interface.  The restart-lifespan layer
sharpens it further to the standard uniform local-existence statement

    UniformH3RealRestartLifespan.

The restart interface is now also normalized to the single canonical scalar
H³ energy

    UniformCanonicalH3RealRestartLifespan.

The two restart formulations are proved equivalent.  The canonical-energy form
is the one closest to the usual local-well-posedness theorem in which lifespan
depends only on the total H³ size of the restart datum.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The canonical H³ closure plus the classical tail-H³ continuation theorem give
the honest seeded vorticity `L¹_t L∞_x` continuation criterion.

Both the velocity-gradient envelope and top-order transport-flux cancellation
are reconstructed internally from canonical H³ data and are no longer public
continuation hypotheses.
-/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    )
    (
      hH3ToExtension :
        H3ControlProducesExtension
    ) :
    SeededVorticityL1LinfProducesExtension := by

  have hLandau :
      EnergyClassProducesLandauTransportAnalytic :=
    energyClassProducesLandauTransportAnalytic_of_canonical
      hCanonical

  apply
    seededVorticityL1LinfProducesExtension_of_H3Factorization

  · exact
      vorticityL1LinfProducesH3Control_of_landauClosure
        hSmooth
        hCanonical
        hLandau
        hEndpoint

  · exact hH3ToExtension

/--
The Landau H³ closure plus a uniform local H³ restart lifespan gives the
honest seeded vorticity `L¹_t L∞_x` continuation criterion.

This eliminates the abstract `H3ControlProducesExtension` hypothesis from the
Landau-facing statement: the remaining continuation input is the concrete
uniform-lifespan local well-posedness frontier.
-/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure_uniformLifespan
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    )
    (
      hUniform :
        UniformH3RealRestartLifespan
    ) :
    SeededVorticityL1LinfProducesExtension := by

  exact
    seededVorticityL1LinfProducesExtension_of_landauClosure
      hSmooth
      hCanonical
      hEndpoint
      (h3ControlProducesExtension_of_uniformLifespan hUniform)


/--
The Landau H³ closure plus a uniform restart lifespan controlled by the single
canonical normalized H³ energy gives the seeded continuation criterion.

All conversion between the componentwise `VelocityH3BoundAt` interface and the
scalar energy ceiling is discharged by `Restart.EnergyLifespan`.
-/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure_canonicalEnergyLifespan
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    )
    (
      hUniform :
        UniformCanonicalH3RealRestartLifespan
    ) :
    SeededVorticityL1LinfProducesExtension := by

  exact
    seededVorticityL1LinfProducesExtension_of_landauClosure_uniformLifespan
      hSmooth
      hCanonical
      hEndpoint
      (uniformH3RealRestartLifespan_of_canonicalEnergy hUniform)


/--
The Landau H³ closure plus the per-energy canonical H³ local-well-posedness
statement gives the seeded continuation criterion.

This is the Landau-facing form with all choice-function packaging removed from
the remaining classical input.
-/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure_localWellPosedness
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hCanonical :
        EnergyClassProducesCanonicalH3Data
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    )
    (
      hLocal :
        CanonicalH3RealLocalWellPosedness
    ) :
    SeededVorticityL1LinfProducesExtension := by

  exact
    seededVorticityL1LinfProducesExtension_of_landauClosure_canonicalEnergyLifespan
      hSmooth
      hCanonical
      hEndpoint
      (uniformCanonicalH3RealRestartLifespan_of_localWellPosedness hLocal)

end Euclidean
end Bridge
end PrimeTensor
