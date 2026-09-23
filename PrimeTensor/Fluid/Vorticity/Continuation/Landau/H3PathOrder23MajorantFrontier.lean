import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderZeroEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneEnergyDerivativeClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrder3SelectedClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathExactEnergyFrontier
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyDerivativeMajorantOnly
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.EnergyDerivativeReducedDomination

/-!
# Reduce the H³ derivative-majorant frontier to orders two and three

Orders zero and one now have exact H³-path energy derivative identities without
using the historical dominated-differentiation majorant package.

The higher mixed-time commutation statements for orders two and three are also
already closed on every admissible H³ path.  Therefore the only remaining
dominated-integral information needed to assemble

    H3OrderEnergyDerivativeIdentities

is the locally uniform integrable majorant data for the order-two and
order-three energy blocks.

This file exposes exactly that smaller frontier and proves that it suffices for
the complete four-order derivative tuple.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-- The only derivative-majorant witnesses still needed after closing the
order-zero and order-one energy derivative identities directly. -/
structure H3Order23EnergyDerivativeMajorantDataAt
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T t : ℝ) : Type where
  order2 :
    H3Order2EnergyDerivativeMajorantOnTailAt u a T t
  order3 :
    H3Order3EnergyDerivativeMajorantOnTailAt u a T t

/-- Path-specific derivative-majorant frontier reduced to the two higher
energy blocks. -/
def H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
          Nonempty
            (H3Order23EnergyDerivativeMajorantDataAt
              u a T t)

/-- The previous four-order path-majorant frontier projects to the genuinely
remaining order-two/order-three package. -/
theorem h3PathEnergyClassProducesOrder23EnergyDerivativeMajorants_of_pathMajorants
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants := by
  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨h⟩

  exact
    ⟨
      {
        order2 := h.order2
        order3 := h.order3
      }
    ⟩

/-- Order-two/order-three majorants are enough for the exact four-order H³
energy derivative identities.

Orders zero and one use their direct closed H³-path theorems.  Orders two and
three use the already-closed mixed-time commutation together with only their
own reduced domination witnesses. -/
theorem h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Majorants
    (hMajorants :
      H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants) :
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
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans hClass.terminal_start.1 ht.1,
        ht.2
      ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  have ha :
      0 < a :=
    hClass.terminal_start.1

  have hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnTail
        u a T :=
    h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail
      u T hH3 a hClass

  have hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnTail
        u a T :=
    h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail
      u T hH3 a hClass

  let hReduced2 :
      H3Order2EnergyDerivativeReducedDominatedOnTailAt
        u a T t :=
    h3Order2ReducedDomination_of_majorant
      hClass ht hMajorant.order2

  let hReduced3 :
      H3Order3EnergyDerivativeReducedDominatedOnTailAt
        u a T t :=
    h3Order3ReducedDomination_of_majorant
      hClass ht hMajorant.order3

  have hDom2 :
      H3Order2EnergyDerivativeDominatedOnTailAt
        u a T t :=
    h3Order2EnergyDerivativeDominatedOnTailAt_of_reduced
      hH3.navier_stokes
      ha
      ht
      hReduced2

  have hDom3 :
      H3Order3EnergyDerivativeDominatedOnTailAt
        u a T t :=
    h3Order3EnergyDerivativeDominatedOnTailAt_of_reduced
      hH3.navier_stokes
      ha
      ht
      hReduced3

  have h2 :
      HasDerivAt
        (velocityH3Energy2At u)
        (velocityH3FormalDerivative2At u t)
        t :=
    hasDerivAt_velocityH3Energy2At_of_tail_mixed_of_tail_dominated
      hMixed2
      hInt
      hDom2

  have h3 :
      HasDerivAt
        (velocityH3Energy3At u)
        (velocityH3FormalDerivative3At u t)
        t :=
    hasDerivAt_velocityH3Energy3At_of_tail_mixed_of_tail_dominated
      hMixed3
      hInt
      hDom3

  exact
    ⟨h0, h1, h2, h3⟩

/-- Consequently the reduced order-two/order-three majorant frontier also
suffices for differentiability of the full canonical H³ energy. -/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_order23Majorants
    (hMajorants :
      H3PathEnergyClassProducesOrder23EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by
  intro u T hH3 a hClass t ht

  have hIds :
      H3OrderEnergyDerivativeIdentities u t :=
    h3PathEnergyClassProducesOrderEnergyDerivativeIdentities_of_order23Majorants
      hMajorants
      u T hH3
      a hClass
      t ht

  have hDeriv :
      deriv (velocityH3EnergyAt u) t
        =
      velocityH3FormalDerivativeAt u t :=
    deriv_velocityH3EnergyAt
      hIds

  rw [hDeriv]

  exact
    hasDerivAt_velocityH3EnergyAt
      hIds

end

end Euclidean
end Bridge
end PrimeTensor
