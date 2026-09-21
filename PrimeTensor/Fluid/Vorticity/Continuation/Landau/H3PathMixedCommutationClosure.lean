import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder3SelectedClosure

/-!
# Remove mixed commutation from the H³-path BKM frontier

The two path-specific mixed-time commutation interfaces are now closed:

* order two by `H3PathOrder2SelectedClosure`;
* order three by `H3PathOrder3SelectedClosure`.

Consequently the scalar H³ energy differentiability theorem no longer needs
mixed commutation as an external hypothesis.  Only the locally uniform
integrable derivative-majorant package remains at that layer.

Substituting this into the already-factored BKM theorem removes mixed
commutation from the public continuation frontier entirely.  The remaining
independent inputs are exactly:

1. a late-tail zeroth-order physical `L²` radius;
2. H³ energy-derivative majorants;
3. canonical H³ gradient growth.

No new estimate, derivative calculation, or selected/old transport argument is
introduced in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-- With both order-two and order-three mixed commutation now closed on the
old H³ path, derivative majorants alone discharge canonical scalar H³ energy
differentiability. -/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_majorants
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by
  exact
    h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderwiseMixed_of_majorants
      h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail
      h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail
      hMajorants

/-- H³-path BKM continuation after completely eliminating mixed-time
commutation as an external hypothesis.

The only remaining interfaces are the low-frequency physical `L²` tail,
derivative majorants, and canonical gradient growth. -/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_majorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_majorants
        hMajorants)
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
