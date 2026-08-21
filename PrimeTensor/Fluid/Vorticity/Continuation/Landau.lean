import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure.Landau.Endpoint
import PrimeTensor.Fluid.Vorticity.Continuation.Frontier

/-!
# Landau H³ continuation factorization

The explicit Landau H³ transport closure has already been carried through the
canonical energy estimate, BKM logarithmic endpoint, and scalar Osgood step to

    VorticityL1LinfProducesH3Control.

The only remaining independent continuation input is therefore the classical
tail-H³ continuation implication

    H3ControlProducesExtension.

This file composes those two pieces using the pre-existing continuation
factorization theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The Landau H³ closure plus the classical tail-H³ continuation theorem gives
the honest seeded vorticity `L¹_t L∞_x` continuation criterion.
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
      hLandau :
        EnergyClassProducesLandauTransportAnalytic
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

  apply
    seededVorticityL1LinfProducesExtension_of_H3Factorization

  · exact
      vorticityL1LinfProducesH3Control_of_landauClosure
        hSmooth
        hCanonical
        hLandau
        hEndpoint

  · exact hH3ToExtension

end Euclidean
end Bridge
end PrimeTensor
