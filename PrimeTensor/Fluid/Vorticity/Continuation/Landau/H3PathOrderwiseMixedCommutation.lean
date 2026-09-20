import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathMixedCommutationFrontier

/-!
# H³-path mixed commutation, split orderwise

`H3PathMixedCommutationFrontier` identified the genuine higher-time calculus
obstruction as

    d/dt (D²u) = D²(∂ₜu),
    d/dt (D³u) = D³(∂ₜu).

That file still stated the commutation frontier globally over every
`PreterminalH3EnergyClass`, although the BKM argument only consumes energy
classes carried by a `LoggedPreterminalH3PathAdmissible` solution.

This file removes that excess quantifier and splits the two derivative orders.

The remaining time-calculus interfaces are now independently:

* order-two mixed commutation on H³-path energy-class tails;
* order-three mixed commutation on H³-path energy-class tails.

Together with the already-isolated derivative majorants they reconstruct the
four scalar H³ energy derivative identities, hence canonical scalar H³ energy
differentiability.

This is useful for the next analytic step because order two can now be closed
without simultaneously solving order three.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/-! ## Orderwise H³-path commutation frontiers -/

/--
Order-two mixed time--space commutation only for energy classes carried by an
H³-path-admissible preterminal solution.
-/
def H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          H3Order2VelocityMixedTimeDerivativeOnTail u a T

/--
Order-three mixed time--space commutation only for energy classes carried by an
H³-path-admissible preterminal solution.
-/
def H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          H3Order3VelocityMixedTimeDerivativeOnTail u a T

/-! ## Compatibility with the former global frontier -/

/--
The former global commutation frontier implies the path-specific order-two
frontier.
-/
theorem h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail_of_global
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail) :
    H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail := by

  intro u T hH3 a hClass

  exact
    (hMixed u a T hClass).1

/--
The former global commutation frontier implies the path-specific order-three
frontier.
-/
theorem h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail_of_global
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail) :
    H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail := by

  intro u T hH3 a hClass

  exact
    (hMixed u a T hClass).2

/-! ## Reconstruct the scalar H³ derivative identities directly -/

/--
Order-two and order-three H³-path commutation plus the existing majorant
frontier give the exact four scalar H³ energy derivative identities.

This proof bypasses the historical global PDE-time frontier entirely.
-/
theorem h3Path_orderEnergyDerivativeIdentities_of_orderwiseMixed_of_majorants
    (hMixed2 :
      H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail)
    (hMixed3 :
      H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T a t : ℝ}
    (hH3 : LoggedPreterminalH3PathAdmissible u T)
    (hClass : PreterminalH3EnergyClass u a T)
    (ht : t ∈ Set.Ioo a T) :
    H3OrderEnergyDerivativeIdentities u t := by

  have hReduced :
      EnergyClassProducesH3EnergyDerivativeReducedDomination :=
    energyClassProducesH3EnergyDerivativeReducedDomination_of_majorants
      hMajorants

  have hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination :=
    energyClassProducesH3EnergyDerivativeTailLocalDomination_of_reduced
      hReduced

  have hOrder2 :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T :=
    hMixed2
      u T hH3
      a hClass

  have hOrder3 :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T :=
    hMixed3
      u T hH3
      a hClass

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

  rcases
    hDom u a T hClass t ht
  with
    ⟨hDomAt⟩

  exact
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
      hH3.navier_stokes
      htAbs
      hInt
      hOrder2
      hOrder3
      hDomAt

/--
The orderwise path-specific commutation frontiers and derivative majorants
discharge canonical scalar H³ energy differentiability.
-/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderwiseMixed_of_majorants
    (hMixed2 :
      H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail)
    (hMixed3 :
      H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by

  intro u T hH3 a hClass t ht

  have hIds :
      H3OrderEnergyDerivativeIdentities u t :=
    h3Path_orderEnergyDerivativeIdentities_of_orderwiseMixed_of_majorants
      hMixed2
      hMixed3
      hMajorants
      hH3
      hClass
      ht

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

/-! ## BKM endpoint with the commutation orders separated -/

/--
BKM continuation with the scalar H³ differentiability input reduced to the
three exact differentiation-under-integral ingredients:

1. order-two H³-path mixed commutation;
2. order-three H³-path mixed commutation;
3. locally uniform integrable derivative majorants.

The low-frequency and canonical gradient-growth interfaces remain independent.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_orderwiseMixed_of_majorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMixed2 :
      H3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail)
    (hMixed3 :
      H3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_orderwiseMixed_of_majorants
        hMixed2
        hMixed3
        hMajorants)
      hGrowth

/--
Backwards-compatible factorization from the former global mixed-commutation
frontier through the two path-specific orderwise interfaces.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_globalMixed_of_majorants_of_growth_via_orderwise
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMixed :
      EnergyClassProducesH3HigherMixedTimeCommutationOnTail)
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by

  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_orderwiseMixed_of_majorants_of_growth
      hLow
      (h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail_of_global
        hMixed)
      (h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail_of_global
        hMixed)
      hMajorants
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
