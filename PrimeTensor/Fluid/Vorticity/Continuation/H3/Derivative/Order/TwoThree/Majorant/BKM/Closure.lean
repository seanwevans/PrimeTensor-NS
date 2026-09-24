import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.TwoThree.Majorant.Frontier
import PrimeTensor.Fluid.Vorticity.Continuation.H3.Energy.Tail.Low.From.Derivative.Identities

/-!
# Reduce H³-path BKM continuation to order-two/order-three derivative majorants

The active exact-energy continuation route has already closed:

* all order-two/order-three mixed time-space commutation;
* the complete physical PDE pairing package;
* full H³ pressure cancellation;
* full H³ diffusion nonpositivity;
* the BKM low-frequency tail once exact orderwise energy differentiation is
  available.

Orders zero and one now also have direct exact energy derivative identities.
The preceding file therefore showed that only the locally uniform integrable
majorants for the order-two and order-three derivative products are needed to
assemble the complete four-order derivative tuple.

This file feeds that reduced tuple into the one-frontier continuation theorem.
Consequently the public H³-path BKM frontier is now exactly

    H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants.

No order-zero/order-one majorant, mixed-commutation, PDE-pairing, pressure-sign,
diffusion-sign, or low-tail hypothesis remains.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- Order-two/order-three derivative majorants alone imply the H³-path BKM
continuation conclusion. -/
theorem h3PathVorticityL1LinfProducesExtension_of_order23Majorants
    (hMajorants :
      H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_derivativeIdentities
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Majorants
        hMajorants)

end

end Euclidean
end Bridge
end PrimeTensor
