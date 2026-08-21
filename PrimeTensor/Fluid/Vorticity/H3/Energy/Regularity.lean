import PrimeTensor.Fluid.Vorticity.BKM.Energy.Endpoint

/-!
# High-order regularity frontier for the H³ energy estimate

The differentiated H³ Navier--Stokes estimate cannot be justified from the
project's current `LoggedPreterminalNavierStokesAdmissible` predicate alone.

That predicate supplies the preterminal equations together with the spatial
regularity needed by the vorticity equation, but an H³ energy derivation
differentiates the momentum equation through order three.  The viscous term
therefore reaches two additional spatial derivatives.

This file makes the missing high-order justification explicit and factors the
energy side of BKM into two independent obligations:

1. a seeded preterminal solution enters a high-order energy class on some
   terminal tail;

2. within that class, the differentiated H³ energy estimate is valid.

The second obligation is the one to attack with integration by parts and
commutator estimates.  The first is the parabolic smoothing / strong-solution
regularity bridge.

No new analytic theorem is assumed implicitly.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/--
High-order spatial regularity of the logged velocity on a terminal tail.

Order five is chosen because applying three spatial derivatives to the
viscous Laplacian reaches fifth spatial derivatives at the pointwise classical
level.  This is intentionally stronger than the H³ norm itself: it is a
justification class for deriving the energy identity, not the quantity whose
growth we ultimately control.
-/
def VelocitySpatialC5OnTail
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop :=
  ∀
    (t : ℝ),
      t ∈ Set.Ico a T →
        ∀
          j
          i
          k : PrimeTensor.Axis Depth.three,
            SpatialC3
              (
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                        fun x : Point3 =>
                          (
                            PrimeTensor.Bridge.logSpaceTimeVectorField
                              u t x
                          ).component j
                      )
                  )
              )

/--
The pressure witness in the preterminal Navier--Stokes system has the spatial
regularity needed after three spatial differentiations of the momentum
equation.
-/
def PressureSpatialC4OnTail
    (p : ℝ → ScalarField3)
    (a T : ℝ) : Prop :=
  ∀
    (t : ℝ),
      t ∈ Set.Ico a T →
        ∀
          i : PrimeTensor.Axis Depth.three,
            SpatialC3
              (
                spatial3.d
                  i
                  (p t)
              )

/--
A high-order classical energy class on a terminal tail.

The structure retains an actual pressure witness for the logged preterminal
Navier--Stokes equations and separately records the stronger spatial
regularity needed by the differentiated energy argument.
-/
structure PreterminalH3EnergyClass
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ) : Prop where

  terminal_start :
    a ∈ Set.Ioo (0 : ℝ) T

  velocity_spatial_five :
    VelocitySpatialC5OnTail
      u a T

  pressure_witness :
    ∃
      pressure : ℝ → ScalarField3,
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          pressure
          T
          ∧
        PressureSpatialC4OnTail
          pressure a T

/--
The smoothing / high-order-justification obligation.

A logged preterminal Navier--Stokes solution with one finite H³ seed should
enter the high-order energy class on some terminal tail beginning at or after
the seed time.

This proposition is deliberately separate from the energy estimate itself.
-/
def H3SeedProducesEnergyClass : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      PreterminalH3Seed
          u T
        →
      ∃ a : ℝ,
        PreterminalH3EnergyClass
          u a T

/--
The actual differentiated H³ energy-estimate obligation.

Once the solution is known to lie in the high-order energy class on `[a,T)`,
and `g` is the supplied vorticity envelope, construct an H³ energy profile and
a velocity-gradient envelope satisfying

    E'(t) ≤ A (1 + |h(t)|) E(t).

The vorticity envelope itself is not used analytically in this step; it is
carried so that this proposition composes directly with the existing BKM
interface.
-/
def EnergyClassProducesH3GradientGrowth : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (a T : ℝ)
    (g : ℝ → ℝ),
      PreterminalH3EnergyClass
          u a T
        →
      MeasureTheory.IntegrableOn
          g
          (Set.Ioo (0 : ℝ) T)
        →
      (
        ∀ t : ℝ,
          t ∈ Set.Ioo (0 : ℝ) T →
            VorticityEnvelope
              u g t
      )
        →
      ∃
        (E h : ℝ → ℝ)
        (A : ℝ),
          0 ≤ A
            ∧
          H3EnergyProfileFrom
            u a T E
            ∧
          EnergyLocallyC1OnTail
            a T E
            ∧
          (
            ∀ t : ℝ,
              t ∈ Set.Ioo a T →
                VelocityGradientEnvelope
                  u h t
          )
            ∧
          H3GradientGrowthInequalityFrom
            a T h E A

/--
The smoothing bridge and the actual differentiated energy estimate compose to
the energy-side proposition used by `VorticityBKMEnergyEndpoint`.
-/
theorem vorticityEnvelopeProducesH3GradientGrowth_of_energyClass
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hEnergy :
        EnergyClassProducesH3GradientGrowth
    ) :
    VorticityEnvelopeProducesH3GradientGrowth := by

  intro
    u T g
    hAdmissible
    hSeed
    hgIntegrable
    hgEnvelope

  obtain
    ⟨
      a,
      hClass
    ⟩ :=
    hSmooth
      u T
      hAdmissible
      hSeed

  obtain
    ⟨
      E,
      h,
      A,
      hA,
      hProfile,
      hC1,
      hGradient,
      hGrowth
    ⟩ :=
    hEnergy
      u a T g
      hClass
      hgIntegrable
      hgEnvelope

  refine
    ⟨
      a,
      E,
      h,
      A,
      hClass.terminal_start,
      hA,
      hProfile,
      hC1,
      hGradient,
      hGrowth
    ⟩

/--
After the regularity split, the entire BKM growth frontier depends on exactly
three named analytic inputs:

1. seeded parabolic smoothing into the high-order energy class;
2. the differentiated H³ energy estimate;
3. the endpoint logarithmic vorticity-to-gradient estimate.
-/
theorem vorticityEnvelopeProducesBKMH3Growth_of_regularized_energy_and_endpoint
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hEnergy :
        EnergyClassProducesH3GradientGrowth
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    ) :
    VorticityEnvelopeProducesBKMH3Growth := by

  apply
    vorticityEnvelopeProducesBKMH3Growth_of_energy_and_endpoint
      (
        vorticityEnvelopeProducesH3GradientGrowth_of_energyClass
          hSmooth
          hEnergy
      )
      hEndpoint

/--
With scalar Osgood already proved, the same three inputs give terminal-tail H³
control.
-/
theorem vorticityL1LinfProducesH3Control_of_regularized_energy_and_endpoint
    (
      hSmooth :
        H3SeedProducesEnergyClass
    )
    (
      hEnergy :
        EnergyClassProducesH3GradientGrowth
    )
    (
      hEndpoint :
        VorticityControlsGradientLogarithmically
    ) :
    VorticityL1LinfProducesH3Control := by

  apply
    vorticityL1LinfProducesH3Control_of_energy_and_endpoint
      (
        vorticityEnvelopeProducesH3GradientGrowth_of_energyClass
          hSmooth
          hEnergy
      )
      hEndpoint

end Euclidean
end Bridge
end PrimeTensor
