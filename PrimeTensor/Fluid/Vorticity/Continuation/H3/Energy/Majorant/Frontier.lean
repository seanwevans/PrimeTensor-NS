import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Commutation.Mixed.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Majorant.Only

/-!
# Restrict the H³ derivative-majorant frontier to actual H³ paths

After closing order-two and order-three mixed commutation, the scalar H³ energy
differentiability layer still exposed

    EnergyClassProducesH3EnergyDerivativeMajorants,

which quantifies over every abstract `PreterminalH3EnergyClass`.

The BKM argument never uses that strength.  It only differentiates energy
classes carried by a `LoggedPreterminalH3PathAdmissible` solution.

This file therefore replaces the global majorant frontier by the exact
path-specific statement consumed by BKM.  At one strict tail time:

* obtain the four majorant-only witnesses;
* reconstruct the reduced domination records;
* reconstruct the tail-local dominated-integral records;
* use the already-closed order-two and order-three path commutation theorems;
* assemble the four scalar H³ energy derivative identities.

No new whole-space estimate is proved here.  This is a quantifier reduction:
the remaining majorant problem is now only for energy classes actually arising
on an admissible H³ path.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

noncomputable section

/--
Path-specific H³ derivative-majorant frontier.

Only energy classes carried by an admissible H³ path are quantified over.
-/
def H3PathEnergyClassProducesH3EnergyDerivativeMajorants : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T : ℝ),
      LoggedPreterminalH3PathAdmissible u T →
      ∀ a : ℝ,
        PreterminalH3EnergyClass u a T →
          ∀ t : ℝ,
            t ∈ Set.Ioo a T →
              Nonempty
                (H3EnergyDerivativeMajorantDataAt
                  u a T t)

/-- The historical global majorant frontier implies the path-specific one. -/
theorem h3PathEnergyClassProducesH3EnergyDerivativeMajorants_of_global
    (hMajorants :
      EnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesH3EnergyDerivativeMajorants := by
  intro u T hH3 a hClass t ht
  exact hMajorants u a T hClass t ht

/--
The path-specific majorant frontier is enough for canonical scalar H³ energy
differentiability, because both higher mixed-time commutation branches are now
closed on H³ paths.
-/
theorem h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_pathMajorants
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants) :
    H3PathEnergyClassProducesCanonicalEnergyDifferentiability := by
  intro u T hH3 a hClass t ht

  rcases
    hMajorants u T hH3 a hClass t ht
  with
    ⟨hMajorant⟩

  have hReduced :
      H3EnergyDerivativeReducedDominationDataAt
        u a T t :=
    {
      order0 :=
        h3Order0ReducedDomination_of_majorant
          hClass ht hMajorant.order0
      order1 :=
        h3Order1ReducedDomination_of_majorant
          hClass ht hMajorant.order1
      order2 :=
        h3Order2ReducedDomination_of_majorant
          hClass ht hMajorant.order2
      order3 :=
        h3Order3ReducedDomination_of_majorant
          hClass ht hMajorant.order3
    }

  have ha :
      0 < a :=
    hClass.terminal_start.1

  have hDom :
      H3EnergyDerivativeTailLocalDominationDataAt
        u a T t :=
    {
      order0 :=
        h3Order0EnergyDerivativeDominatedAt_of_reducedOnTail
          hH3.navier_stokes
          ha
          ht
          hReduced.order0
      order1 :=
        h3Order1EnergyDerivativeDominatedAt_of_reducedOnTail
          hH3.navier_stokes
          ha
          ht
          hReduced.order1
      order2 :=
        h3Order2EnergyDerivativeDominatedOnTailAt_of_reduced
          hH3.navier_stokes
          ha
          ht
          hReduced.order2
      order3 :=
        h3Order3EnergyDerivativeDominatedOnTailAt_of_reduced
          hH3.navier_stokes
          ha
          ht
          hReduced.order3
    }

  have hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T :=
    h3PathEnergyClassProducesOrder2MixedTimeCommutationOnTail
      u T hH3 a hClass

  have hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T :=
    h3PathEnergyClassProducesOrder3MixedTimeCommutationOnTail
      u T hH3 a hClass

  have htAbs :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans hClass.terminal_start.1 ht.1,
      ht.2
    ⟩

  have hInt :
      VelocityH3IntegrableAt u t :=
    hH3.velocity_h3_integrable
      t htAbs

  have hIds :
      H3OrderEnergyDerivativeIdentities u t :=
    h3OrderEnergyDerivativeIdentities_of_integrable_of_tailLocalInputs
      hH3.navier_stokes
      htAbs
      hInt
      hMixed2
      hMixed3
      hDom

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

/--
BKM continuation with the derivative-majorant hypothesis reduced to actual
H³-path energy classes.

The remaining public interfaces are now:

1. a late-tail zeroth-order physical `L²` radius;
2. path-specific locally uniform integrable H³ derivative majorants;
3. canonical H³ gradient growth.
-/
theorem h3PathVorticityL1LinfProducesExtension_of_lowTail_of_pathMajorants_of_growth
    (hLow :
      H3PathEnergyClassProducesBKMZerothVelocityL2LateTail)
    (hMajorants :
      H3PathEnergyClassProducesH3EnergyDerivativeMajorants)
    (hGrowth :
      H3PathEnergyClassProducesCanonicalGradientGrowth) :
    H3PathVorticityL1LinfProducesExtension := by
  exact
    h3PathVorticityL1LinfProducesExtension_of_lowTail_of_energyDynamics
      hLow
      (h3PathEnergyClassProducesCanonicalEnergyDifferentiability_of_pathMajorants
        hMajorants)
      hGrowth

end

end Euclidean
end Bridge
end PrimeTensor
