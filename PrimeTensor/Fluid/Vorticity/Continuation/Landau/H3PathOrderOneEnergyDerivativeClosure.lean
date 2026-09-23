import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedTemporalL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedStrongL2FromCoefficientContinuity

/-!
# Close the canonical order-one H³ energy derivative identity

The selected mixed-temporal coefficient continuity frontier is now closed.
The generic strong-`L²` reduction therefore applies without any remaining
hypothesis.

This file exports the three closure statements consumed downstream:

* selected restart-relative strong `L²` differentiation of every first jet;
* the selected order-one energy derivative frontier on the restart radius;
* the absolute old-path order-one H³ energy derivative identity at every
  strict energy-class time.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable section

/-- The selected first spatial jets have their canonical mixed-temporal
coefficient as a genuine restart-relative strong physical `L²` derivative. -/
theorem h3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius_closed :
    H3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius := by
  exact
    h3CanonicalSelectedOrder1RelativePhysicalL2StrongDerivativeOnRestartRadius_of_temporalCoefficientContinuous
      h3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius_closed

/-- The canonical selected order-one scalar energy has its exact derivative on
the complete open restart interval. -/
theorem h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_closed :
    H3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius := by
  exact
    h3CanonicalSelectedOrder1EnergyDerivativeOnRestartRadius_of_temporalCoefficientContinuous
      h3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius_closed

/-- The canonical first-order H³ energy has its exact formal derivative at
every strict time of every H³ energy class. -/
theorem h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_closed
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a s : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (hs : s ∈ Set.Ioo a T) :
    HasDerivAt
      (velocityH3Energy1At u)
      (velocityH3FormalDerivative1At u s)
      s := by
  exact
    h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_of_selectedTemporalCoefficientContinuous
      h3CanonicalSelectedOrder1RelativeTemporalScalarL2ContinuousOnRestartRadius_closed
      hH3 hClass hs

end

end Euclidean
end Bridge
end PrimeTensor
