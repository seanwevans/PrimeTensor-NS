import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderThreeEnergyDerivativeClosure

/-!
# Close the H³-path BKM continuation criterion

The last outstanding exact energy identity, the order-three block, is now
closed.  Therefore the four orderwise H³ energy derivative identities assemble
without additional analytic hypotheses, and the existing reduction from those
identities to the BKM continuation criterion applies outright.

This closes the current `LoggedPreterminalH3PathAdmissible` continuation route:

    LoggedPreterminalH3PathAdmissible u T
      + VorticityL1LinfControl u T
      ⇒ SmoothContinuationExtension through T.

No extra orderwise derivative, low-tail, pressure, commutation, majorant, or
selected-restart hypothesis remains at the public endpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- All four exact old-path H³ energy derivative identities are now closed. -/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_closed :
    H3PathEnergyClassProducesOrderEnergyDerivativeIdentities := by

  exact
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order3Identity
      h3PathEnergyClassProducesOrder3EnergyDerivativeIdentity_closed

/-- The H³-path BKM continuation criterion is closed with no remaining
auxiliary analytic frontier. -/
theorem h3PathVorticityL1LinfProducesExtension_closed :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_order3EnergyDerivativeIdentity
      h3PathEnergyClassProducesOrder3EnergyDerivativeIdentity_closed

end

end Euclidean
end Bridge
end PrimeTensor
