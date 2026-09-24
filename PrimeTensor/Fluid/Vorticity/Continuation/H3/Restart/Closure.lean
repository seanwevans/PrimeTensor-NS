import PrimeTensor.Fluid.Vorticity.Continuation.H3.Core
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Late.Restart.Tail.Control.Closure

/-!
# Close the H³-path Landau continuation restart

`Continuation.Landau.H3Path` removed the obsolete
`H3SeedProducesEnergyClass` hypothesis from the BKM energy side by working in
the correct strong-solution class

    LoggedPreterminalH3PathAdmissible u T.

Its factorized continuation theorem still accepted an abstract

    H3ControlProducesExtension

input.

That last layer is already closed elsewhere in the repository.  The
pressure-free late-restart theorem

    h3ControlProducesExtension_of_unitViscosityCanonicalEnergy

shows that terminal-tail H³ control yields a genuine continuation using only

    EnergyClassProducesCanonicalH3Data.

Therefore the same canonical-energy hypothesis already used by the Landau
energy estimate also closes the restart half.

This file packages the resulting two-input H³-path BKM theorem:

* canonical H³ energy-data closure;
* logarithmic vorticity-to-gradient endpoint.

No smoothing axiom, old-pressure frontier, abstract continuation theorem, or
separate local-well-posedness/lifespan hypothesis remains in this statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Closed-restart Landau/BKM continuation criterion on the standard preterminal
H³ path class.

The same `hCanonical` hypothesis is used twice:

1. on the energy side, to derive the explicit Landau H³ differential
   inequality;
2. on the continuation side, to build the pressure-free late spectral restart
   from the terminal H³ bound produced by BKM/Osgood.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_landauClosure_closedRestart
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hEndpoint :
      VorticityControlsGradientLogarithmically) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_landauClosure
      hCanonical
      hEndpoint
      (h3ControlProducesExtension_of_unitViscosityCanonicalEnergy
        hCanonical)

/--
Expanded factorization of the same result.

This theorem makes explicit that the BKM estimate and the pressure-free
continuation construction meet exactly at `TerminalTailH3Control`.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_landauH3Control_and_closedRestart
    (hCanonical :
      EnergyClassProducesCanonicalH3Data)
    (hEndpoint :
      VorticityControlsGradientLogarithmically) :
    H3PathVorticityL1LinfProducesExtension := by

  have hH3 :
      H3PathVorticityL1LinfProducesH3Control :=
    h3PathVorticityL1LinfProducesH3Control_of_landauClosure
      hCanonical
      hEndpoint

  have hContinue :
      H3ControlProducesExtension :=
    h3ControlProducesExtension_of_unitViscosityCanonicalEnergy
      hCanonical

  exact
    h3PathVorticityL1LinfProducesExtension_of_H3Factorization
      hH3
      hContinue

end Euclidean
end Bridge
end PrimeTensor
