import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderZeroEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder23MajorantFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathLowTailFromDerivativeIdentities

/-!
# Reduce H³-path BKM continuation to the order-two/order-three energy identities

Orders zero and one now have direct exact energy derivative identities on every
admissible H³ path.  The low-frequency BKM tail is already automatic once the
complete orderwise derivative tuple is known, and all fixed-time spatial
pairing/sign frontiers are closed.

Thus the genuinely remaining energy-differentiation content is just

    d/dt E₂ = F₂,
    d/dt E₃ = F₃.

This file packages those two statements as the active continuation frontier.
It removes the stronger pointwise-in-space majorant interface from the public
endpoint and prepares the higher orders for the same Hilbert-space strong-L²
strategy that closed order one.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable section

/-- Exact derivative identities for only the two still-unclosed H³ energy
blocks. -/
def H3PathEnergyClassProducesOrder23EnergyDerivativeIdentities : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
          HasDerivAt
              (velocityH3Energy2At u)
              (velocityH3FormalDerivative2At u t)
              t
            ∧
          HasDerivAt
              (velocityH3Energy3At u)
              (velocityH3FormalDerivative3At u t)
              t

/-- Orders zero and one are closed outright, so the order-two/order-three pair
assembles the complete four-order derivative tuple. -/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Identities
    (h23 :
      H3PathEnergyClassProducesOrder23EnergyDerivativeIdentities) :
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

  rcases
    h23 u T hH3 a hClass t ht
  with
    ⟨h2, h3⟩

  exact
    ⟨h0, h1, h2, h3⟩

/-- The active H³-path BKM endpoint can therefore be stated using only the two
higher exact energy derivative identities. -/
theorem h3PathVorticityL1LinfProducesExtension_of_order23EnergyDerivativeIdentities
    (h23 :
      H3PathEnergyClassProducesOrder23EnergyDerivativeIdentities) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_derivativeIdentities
      (h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Identities
        h23)

/-- Compatibility: the previous order-two/order-three majorant frontier implies
the new exact-identity frontier. -/
theorem h3PathEnergyClassProducesOrder23EnergyDerivativeIdentities_of_order23Majorants
    (hMajorants :
      H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesOrder23EnergyDerivativeIdentities := by
  intro u T hH3 a hClass t ht

  have hAll :
      H3OrderEnergyDerivativeIdentities u t :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Majorants
      hMajorants
      u T hH3
      a hClass
      t ht

  exact
    ⟨hAll.2.2.1, hAll.2.2.2⟩

end

end Euclidean
end Bridge
end PrimeTensor
