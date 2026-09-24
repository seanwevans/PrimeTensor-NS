import PrimeTensor.Fluid.Vorticity.BKM.Endpoint.Canonical.Actual.Gradient.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Curl.Weak.FTC.Global.Closure

/-!
# BKM endpoint: canonical selected continuation closure

The canonical selected BKM endpoint now proves terminal H³ control from only

* `H3SeedProducesEnergyClass`;
* `EnergyClassProducesCanonicalH3Data`.

The continuation tree has independently closed the remaining restart theorem:

    h3ControlProducesExtension_tailH3_curl :
      H3ControlProducesExtension.

That theorem is pressure-free and comes from the selected/old weak--strong
curl weak-FTC chain.

This file simply composes the two completed branches.  No external logarithmic
gradient endpoint and no separate `H3ControlProducesExtension` hypothesis
remain.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/--
Canonical selected BKM harmonic analysis plus the pressure-free curl weak-FTC
restart closure prove the seeded vorticity continuation criterion.

The only remaining named inputs are the smoothing/high-order-entry bridge and
the canonical H³ tail-data bridge.
-/
theorem seededVorticityL1LinfProducesExtension_of_canonical_selected_endpoint_closed
    (hSmooth : H3SeedProducesEnergyClass)
    (hCanonical : EnergyClassProducesCanonicalH3Data) :
    SeededVorticityL1LinfProducesExtension := by

  exact
    seededVorticityL1LinfProducesExtension_of_canonical_selected_endpoint
      hSmooth
      hCanonical
      h3ControlProducesExtension_tailH3_curl

end

end Euclidean
end Bridge
end PrimeTensor
