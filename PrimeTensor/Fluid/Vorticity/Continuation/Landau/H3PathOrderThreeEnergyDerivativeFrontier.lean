import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderTwoEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder23EnergyDerivativeFrontier

/-!
# Reduce H³-path BKM continuation to the order-three energy identity alone

Orders zero, one, and two now have exact old-path scalar energy derivative
identities on every admissible H³ energy-class interval.

Therefore the complete H³ derivative tuple is missing only

    d/dt E₃(u,t) = F₃(u,t).

This file promotes that fact to the public continuation boundary.  In
particular, the BKM endpoint no longer assumes anything about the order-two
energy block.

No new analytic estimate is proved here; this is the exact logical reduction
made possible by the closed order-two Hilbert-space argument.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- The sole remaining exact scalar H³ energy derivative identity. -/
def H3PathEnergyClassProducesOrder3EnergyDerivativeIdentity : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
          HasDerivAt
            (velocityH3Energy3At u)
            (velocityH3FormalDerivative3At u t)
            t

/-- The closed order-zero, order-one, and order-two identities together with
the sole remaining order-three identity assemble the complete orderwise H³
energy derivative tuple. -/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order3Identity
    (h3 :
      H3PathEnergyClassProducesOrder3EnergyDerivativeIdentity) :
    H3PathEnergyClassProducesOrderEnergyDerivativeIdentities := by

  intro u T hH3 a hClass t ht

  have h0 :
      HasDerivAt
        (velocityH3Energy0At u)
        (velocityH3FormalDerivative0At u t)
        t :=
    h3PathEnergyClassProducesOrder0EnergyDerivativeIdentity_closed
      hH3 hClass ht

  have h1 :
      HasDerivAt
        (velocityH3Energy1At u)
        (velocityH3FormalDerivative1At u t)
        t :=
    h3PathEnergyClassProducesOrder1EnergyDerivativeIdentity_closed
      hH3 hClass ht

  have h2 :
      HasDerivAt
        (velocityH3Energy2At u)
        (velocityH3FormalDerivative2At u t)
        t :=
    h3PathEnergyClassProducesOrder2EnergyDerivativeIdentity_closed
      hH3 hClass ht

  have h3' :
      HasDerivAt
        (velocityH3Energy3At u)
        (velocityH3FormalDerivative3At u t)
        t :=
    h3 u T hH3 a hClass t ht

  exact
    ⟨h0, h1, h2, h3'⟩

/-- The active H³-path BKM continuation endpoint now consumes only the exact
order-three scalar energy derivative identity. -/
theorem h3PathVorticityL1LinfProducesExtension_of_order3EnergyDerivativeIdentity
    (h3 :
      H3PathEnergyClassProducesOrder3EnergyDerivativeIdentity) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_derivativeIdentities
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order3Identity
        h3)

/-- Compatibility: the previous order-two/order-three exact-identity frontier
implies the new order-three-only frontier by projection. -/
theorem h3PathEnergyClassProducesOrder3EnergyDerivativeIdentity_of_order23Identities
    (h23 :
      H3PathEnergyClassProducesOrder23EnergyDerivativeIdentities) :
    H3PathEnergyClassProducesOrder3EnergyDerivativeIdentity := by

  intro u T hH3 a hClass t ht

  exact
    (h23 u T hH3 a hClass t ht).2

/-- Compatibility: the previous order-two/order-three majorant frontier also
implies the new order-three-only exact identity frontier. -/
theorem h3PathEnergyClassProducesOrder3EnergyDerivativeIdentity_of_order23Majorants
    (hMajorants :
      H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesOrder3EnergyDerivativeIdentity := by

  exact
    h3PathEnergyClassProducesOrder3EnergyDerivativeIdentity_of_order23Identities
      (h3PathEnergyClassProducesOrder23EnergyDerivativeIdentities_of_order23Majorants
        hMajorants)

end

end Euclidean
end Bridge
end PrimeTensor
