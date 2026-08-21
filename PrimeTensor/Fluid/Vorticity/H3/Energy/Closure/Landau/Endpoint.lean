import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure.Landau

/-!
# Landau H³ BKM endpoint closure

This file carries the explicit Landau H³ transport closure through the
pre-existing logarithmic endpoint and scalar Osgood machinery.

No new PDE estimate is introduced here.  The only inputs beyond the Landau
energy closure are the already isolated logarithmic
vorticity-to-gradient endpoint estimate and the seeded smoothing bridge.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The explicit Landau H³ energy closure together with the logarithmic
vorticity-to-gradient endpoint gives the existing BKM H³ growth proposition.
-/
theorem vorticityEnvelopeProducesBKMH3Growth_of_landauClosure
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
    ) :
    VorticityEnvelopeProducesBKMH3Growth := by

  apply
    vorticityEnvelopeProducesBKMH3Growth_of_energy_and_endpoint
      (
        vorticityEnvelopeProducesH3GradientGrowth_of_landauClosure
          hSmooth
          hCanonical
          hLandau
      )
      hEndpoint

/--
With scalar Osgood already available in the existing regularity layer, the
same Landau closure inputs give terminal-tail H³ control from an integrable
vorticity envelope.
-/
theorem vorticityL1LinfProducesH3Control_of_landauClosure
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
    ) :
    VorticityL1LinfProducesH3Control := by

  apply
    vorticityL1LinfProducesH3Control_of_energy_and_endpoint
      (
        vorticityEnvelopeProducesH3GradientGrowth_of_landauClosure
          hSmooth
          hCanonical
          hLandau
      )
      hEndpoint

end Euclidean
end Bridge
end PrimeTensor
