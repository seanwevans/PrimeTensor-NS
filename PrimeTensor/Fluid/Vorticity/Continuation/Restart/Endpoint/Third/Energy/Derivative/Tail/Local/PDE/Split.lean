import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Energy.Derivative.Tail.Local.Assembly

/-!
# Split the tail-local H³ energy derivative frontier into PDE time regularity and domination

After `EnergyDerivativeTailLocalAssembly`, the only order-two/order-three
mixed-time assumptions live on the actual high-order energy-class tail.

The temporal-RHS and tail-local orderwise files sharpen those assumptions
further.  The derivative values are already known from Navier--Stokes:

    D²(∂ₜu) = momentumRHS2Component,
    D³(∂ₜu) = momentumRHS3Component.

So the genuine higher mixed-time obligation can be stated in the PDE-native
form

    d/dt (D²u) = momentumRHS2Component,
    d/dt (D³u) = momentumRHS3Component.

This file separates that local PDE time-regularity problem from the independent
whole-space dominated-differentiation problem and proves that the two together
recover the tail-local derivative assembly and hence continuation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- On every high-order energy-class tail, any pressure witness carried by the
class gives the explicit PDE-form order-two and order-three time derivatives. -/
def EnergyClassProducesH3HigherTimeDerivativePDEOnTail : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        ∀ p : ℝ → ScalarField3,
          PreterminalNavierStokes3
              (logSpaceTimeVectorField u)
              p
              T →
            PressureSpatialC4OnTail p a T →
              H3Order2VelocityTimeDerivativePDEOnTail
                  u p a T
                ∧
              H3Order3VelocityTimeDerivativePDEOnTail
                  u p a T

/-- Independent whole-space differentiation-under-integral frontier on the
high-order tail.  Orders two and three carry tail-contained time
neighborhoods; orders zero and one retain their existing domination data. -/
def EnergyClassProducesH3EnergyDerivativeTailLocalDomination : Prop :=
  ∀
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (a T : ℝ),
      PreterminalH3EnergyClass u a T →
        ∀ t : ℝ,
          t ∈ Set.Ioo a T →
            Nonempty
              (H3EnergyDerivativeTailLocalDominationDataAt
                u a T t)

/-- PDE-form higher time regularity plus tail-local domination reconstruct the
exact input consumed by `EnergyDerivativeTailLocalAssembly`. -/
theorem energyClassProducesH3EnergyDerivativeTailLocalInputs_of_pde_of_domination
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination) :
    EnergyClassProducesH3EnergyDerivativeTailLocalInputs := by
  intro u a T hClass

  rcases hClass.pressure_witness with
    ⟨p, hPDE, hPressure⟩

  rcases hTime u a T hClass p hPDE hPressure with
    ⟨hTime2, hTime3⟩

  have hMixed2 :
      H3Order2VelocityMixedTimeDerivativeOnTail u a T :=
    h3Order2VelocityMixedTimeDerivativeOnTail_of_pde
      hPDE
      hClass.terminal_start.1
      hTime2

  have hMixed3 :
      H3Order3VelocityMixedTimeDerivativeOnTail u a T :=
    h3Order3VelocityMixedTimeDerivativeOnTail_of_pde
      hPDE
      hClass.terminal_start.1
      hTime3

  exact
    ⟨
      hMixed2,
      hMixed3,
      hDom u a T hClass
    ⟩

/-- Real restart from smoothing, explicit tail-local PDE time derivatives, and
the independent tail-local domination frontier. -/
theorem h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailLocalPDE
    (hSmooth : H3SeedProducesEnergyClass)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination) :
    H3ControlProducesRealRestart := by
  exact
    h3ControlProducesRealRestart_of_unitViscositySmoothingEnergyDerivativeTailLocalInputs
      hSmooth
      (energyClassProducesH3EnergyDerivativeTailLocalInputs_of_pde_of_domination
        hTime
        hDom)

/-- Pressure-free continuation with the remaining H³ energy analysis split into
exactly two independent tail-local fronts:

1. higher PDE time differentiability;
2. whole-space differentiation-under-integral domination.
-/
theorem h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailLocalPDE
    (hSmooth : H3SeedProducesEnergyClass)
    (hTime :
      EnergyClassProducesH3HigherTimeDerivativePDEOnTail)
    (hDom :
      EnergyClassProducesH3EnergyDerivativeTailLocalDomination) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscositySmoothingEnergyDerivativeTailLocalInputs
      hSmooth
      (energyClassProducesH3EnergyDerivativeTailLocalInputs_of_pde_of_domination
        hTime
        hDom)

end

end Euclidean
end Bridge
end PrimeTensor
