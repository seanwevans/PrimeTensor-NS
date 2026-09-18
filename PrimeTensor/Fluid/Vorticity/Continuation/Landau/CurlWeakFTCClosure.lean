import PrimeTensor.Fluid.Vorticity.Continuation.Landau
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongCurlWeakFTCGlobalClosure

/-!
# Landau continuation with the continuation/restart frontier discharged by curl weak FTC

The pressure-free curl/vorticity route now proves

    H3ControlProducesExtension

outright from the canonical H³ terminal-tail data.

Therefore the Landau/BKM factorization no longer needs any continuation-
specific hypothesis: neither the old-pressure frontier, nor a uniform restart
lifespan, nor an abstract local-well-posedness assumption occurs in the
Landau-facing seeded continuation theorem below.

The remaining hypotheses are exactly the Landau-side analytic interfaces:

* `H3SeedProducesEnergyClass`;
* `EnergyClassProducesCanonicalH3Data`;
* `EnergyClassProducesGradientEnvelope`;
* `VorticityControlsGradientLogarithmically`.

Under those four inputs, finite `L¹_t L∞_x` vorticity control implies extension.

For the stronger statement that every seeded preterminal solution extends, one
still needs the separate a-priori assertion

    SeededPreterminalNavierStokesForcesVorticityL1Linf.

That distinction is intentional: closing the restart/continuation half is not
the same as proving the global a-priori vorticity bound.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- The pressure-free curl weak-FTC closure removes the final
continuation-specific hypothesis from the Landau/BKM seeded continuation
criterion. -/
theorem seededVorticityL1LinfProducesExtension_of_landauClosure_tailH3_curl
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hGradient :
      EnergyClassProducesGradientEnvelope)
    (hEndpoint :
      VorticityControlsGradientLogarithmically) :
    SeededVorticityL1LinfProducesExtension := by
  exact
    seededVorticityL1LinfProducesExtension_of_landauClosure
      hSmooth
      hCanonical
      hGradient
      hEndpoint
      h3ControlProducesExtension_tailH3_curl

/-- With the remaining a-priori vorticity frontier supplied, the same closure
gives extension of every seeded preterminal Navier--Stokes solution. -/
theorem everySeededPreterminalSolutionExtends_of_landauClosure_tailH3_curl
    (hSmooth :
      H3SeedProducesEnergyClass)
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hGradient :
      EnergyClassProducesGradientEnvelope)
    (hEndpoint :
      VorticityControlsGradientLogarithmically)
    (hApriori :
      SeededPreterminalNavierStokesForcesVorticityL1Linf) :
    EverySeededPreterminalNavierStokesSolutionExtends := by
  exact
    everySeededPreterminalSolutionExtends_of_vorticityCriterion
      (seededVorticityL1LinfProducesExtension_of_landauClosure_tailH3_curl
        hSmooth
        hCanonical
        hGradient
        hEndpoint)
      hApriori

end Euclidean
end Bridge
end PrimeTensor
