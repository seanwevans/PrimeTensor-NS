import PrimeTensor.Fluid.Vorticity.H3.Energy.Divergence

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
At a strict tail time, a preterminal H³ energy-class velocity annihilates the
full pressure contribution to the canonical H³ energy derivative for every
pressure field satisfying the exact whole-space integration-by-parts package.

The only analytic hypothesis retained here is
`H3PressureIntegrationByPartsAt`; differentiated incompressibility is supplied
by `PreterminalH3EnergyClass`.
-/
theorem preterminalH3EnergyClass_pressureDerivative_eq_zero
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hIBP :
        H3PressureIntegrationByPartsAt
          u p t
    ) :
    velocityH3PressureDerivativeAt
        u p t
      =
    0 := by

  apply
    velocityH3PressureDerivativeAt_eq_zero
      hIBP

  exact
    preterminalH3EnergyClass_produces_differentiatedIncompressibility
      hClass ht

/--
Packaged pressure cancellation statement for an H³ energy-class velocity at a
strict tail time.
-/
def H3EnergyClassPressureCancellationAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T t : ℝ) : Prop :=
  ∀ p :
      PrimeTensor.SpaceTimeScalarField
        ℝ ℝ ℝ Depth.three,
    H3PressureIntegrationByPartsAt
        u p t
      →
    velocityH3PressureDerivativeAt
        u p t
      =
    0

/--
Every preterminal H³ energy-class velocity has packaged pressure cancellation
at each strict tail time.
-/
theorem preterminalH3EnergyClass_produces_pressureCancellation
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    ) :
    H3EnergyClassPressureCancellationAt
      u a T t := by

  intro p hIBP

  exact
    preterminalH3EnergyClass_pressureDerivative_eq_zero
      hClass ht hIBP

end Euclidean
end Bridge
end PrimeTensor
