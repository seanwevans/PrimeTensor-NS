import PrimeTensor.Fluid.Vorticity.H3.Energy.Derivative
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation

/-!
# Substituting Navier--Stokes into the canonical H³ energy derivative

The canonical formal energy derivative is

    2 Σ_{|α|≤3,j} ∫ (∂^α v_j) (∂^α ∂ₜ v_j),

where `v = log u`.

This file replaces every temporal factor by the preterminal Navier--Stokes
right-hand side.

A useful point is that only the already-proved first spatial derivative
identity

    PreterminalNavierStokes3.spatial_d_temporalComponent

is needed.  Equality of second- and third-order derivative fields follows by
applying `congrArg (spatial3.d i)` to equality of the lower-order fields.
Thus this module performs no new analytic differentiation rule; it is exact
substitution algebra.

The resulting quantity `velocityH3PDEDerivativeAt` is the concrete object whose
three pieces -- diffusion, transport, and pressure -- will be estimated next.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3PDEDecomposition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
Order-zero right-hand side of the normalized preterminal momentum equation.
-/
noncomputable def momentumRHS0Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          (v t y).component j)
        x
      -
    realAdvectionComponent
        v t x j
      -
    spatial3.d
        j
        (p t)
        x

/--
Order-one right-hand side, in exactly the form supplied by
`spatial_d_temporalComponent`.
-/
noncomputable def momentumRHS1Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  fun x =>
    spatial3.d
        i
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun y =>
              (v t y).component j)
        )
        x
      -
    spatial3.d
        i
        (
          fun y =>
            realAdvectionComponent
              v t y j
        )
        x
      -
    spatial3.d
        i
        (
          spatial3.d
            j
            (p t)
        )
        x

/-- Order-two right-hand side, obtained by differentiating the order-one field. -/
noncomputable def momentumRHS2Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (momentumRHS1Component v p t k j)

/-- Order-three right-hand side, obtained by differentiating twice more. -/
noncomputable def momentumRHS3Component
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three) :
    ScalarField3 :=
  spatial3.d
    i
    (
      spatial3.d
        k
        (momentumRHS1Component v p t l j)
    )

/--
Order-zero temporal field equals the momentum right-hand side.
-/
theorem loggedVelocityTemporalComponent_eq_momentumRHS0
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (j : PrimeTensor.Axis Depth.three) :
    loggedVelocityTemporalComponent
        u t j
      =
    momentumRHS0Component
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        p t j := by

  funext x

  simpa only [
    loggedVelocityTemporalComponent,
    momentumRHS0Component
  ] using
    s.temporalComponent_eq_laplacian_sub_advection_sub_pressure
      ht x j

/--
First spatial derivative of the temporal field equals the order-one momentum
right-hand side.
-/
theorem spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (i j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (loggedVelocityTemporalComponent u t j)
      =
    momentumRHS1Component
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        p t i j := by

  funext x

  change
    spatial3.d
        i
        (
          fun q =>
            temporal.d
              (
                fun τ =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u τ q
                  ).component j
              )
              t
        )
        x
      =
    spatial3.d
        i
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun q =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t q
                ).component j
            )
        )
        x
      -
    spatial3.d
        i
        (
          fun q =>
            realAdvectionComponent
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t q j
        )
        x
      -
    spatial3.d
        i
        (
          spatial3.d
            j
            (p t)
        )
        x

  exact
    s.spatial_d_temporalComponent
      ht x i j

/--
Second spatial derivative substitution follows functorially from the first
derivative field equality.
-/
theorem spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (i k j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          spatial3.d
            k
            (loggedVelocityTemporalComponent u t j)
        )
      =
    momentumRHS2Component
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        p t i k j := by

  have h1 :
      spatial3.d
          k
          (loggedVelocityTemporalComponent u t j)
        =
      momentumRHS1Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t k j :=
    spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
      s ht k j

  have h2 :=
    congrArg
      (spatial3.d i)
      h1

  simpa only [
    momentumRHS2Component
  ] using
    h2

/--
Third spatial derivative substitution follows by one more application of
`spatial3.d` to the second-order field equality.
-/
theorem spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (i k l j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        i
        (
          spatial3.d
            k
            (
              spatial3.d
                l
                (loggedVelocityTemporalComponent u t j)
            )
        )
      =
    momentumRHS3Component
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            u
        )
        p t i k l j := by

  have h2 :
      spatial3.d
          k
          (
            spatial3.d
              l
              (loggedVelocityTemporalComponent u t j)
          )
        =
      momentumRHS2Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t k l j :=
    spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
      s ht k l j

  have h3 :=
    congrArg
      (spatial3.d i)
      h2

  simpa only [
    momentumRHS2Component,
    momentumRHS3Component
  ] using
    h3

/-- PDE-substituted zeroth-order energy derivative. -/
noncomputable def velocityH3PDEDerivative0At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    spatialEnergyPairing
      (loggedVelocityComponent u t j)
      (
        momentumRHS0Component
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p t j
      )

/-- PDE-substituted first-order energy derivative. -/
noncomputable def velocityH3PDEDerivative1At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      spatialEnergyPairing
        (
          spatial3.d
            i
            (loggedVelocityComponent u t j)
        )
        (
          momentumRHS1Component
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            p t i j
        )

/-- PDE-substituted second-order energy derivative. -/
noncomputable def velocityH3PDEDerivative2At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        spatialEnergyPairing
          (
            spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
          )
          (
            momentumRHS2Component
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              p t i k j
          )

/-- PDE-substituted third-order energy derivative. -/
noncomputable def velocityH3PDEDerivative3At
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  ∑ j : PrimeTensor.Axis Depth.three,
    ∑ i : PrimeTensor.Axis Depth.three,
      ∑ k : PrimeTensor.Axis Depth.three,
        ∑ l : PrimeTensor.Axis Depth.three,
          spatialEnergyPairing
            (
              spatial3.d
                i
                (
                  spatial3.d
                    k
                    (
                      spatial3.d
                        l
                        (loggedVelocityComponent u t j)
                    )
                )
            )
            (
              momentumRHS3Component
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u
                )
                p t i k l j
            )

/-- Full PDE-substituted canonical H³ energy derivative. -/
noncomputable def velocityH3PDEDerivativeAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : ℝ :=
  velocityH3PDEDerivative0At u p t
    + velocityH3PDEDerivative1At u p t
    + velocityH3PDEDerivative2At u p t
    + velocityH3PDEDerivative3At u p t

theorem velocityH3FormalDerivative0At_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    velocityH3FormalDerivative0At u t
      =
    velocityH3PDEDerivative0At u p t := by

  unfold
    velocityH3FormalDerivative0At
    velocityH3PDEDerivative0At

  apply Finset.sum_congr rfl

  intro j hj

  rw [
    loggedVelocityTemporalComponent_eq_momentumRHS0
      s ht j
  ]

theorem velocityH3FormalDerivative1At_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    velocityH3FormalDerivative1At u t
      =
    velocityH3PDEDerivative1At u p t := by

  unfold
    velocityH3FormalDerivative1At
    velocityH3PDEDerivative1At

  apply Finset.sum_congr rfl

  intro j hj

  apply Finset.sum_congr rfl

  intro i hi

  rw [
    spatial_d_loggedVelocityTemporalComponent_eq_momentumRHS1
      s ht i j
  ]

theorem velocityH3FormalDerivative2At_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    velocityH3FormalDerivative2At u t
      =
    velocityH3PDEDerivative2At u p t := by

  unfold
    velocityH3FormalDerivative2At
    velocityH3PDEDerivative2At

  apply Finset.sum_congr rfl

  intro j hj

  apply Finset.sum_congr rfl

  intro i hi

  apply Finset.sum_congr rfl

  intro k hk

  rw [
    spatial_d2_loggedVelocityTemporalComponent_eq_momentumRHS2
      s ht i k j
  ]

theorem velocityH3FormalDerivative3At_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    velocityH3FormalDerivative3At u t
      =
    velocityH3PDEDerivative3At u p t := by

  unfold
    velocityH3FormalDerivative3At
    velocityH3PDEDerivative3At

  apply Finset.sum_congr rfl

  intro j hj

  apply Finset.sum_congr rfl

  intro i hi

  apply Finset.sum_congr rfl

  intro k hk

  apply Finset.sum_congr rfl

  intro l hl

  rw [
    spatial_d3_loggedVelocityTemporalComponent_eq_momentumRHS3
      s ht i k l j
  ]

/--
Exact order-zero through order-three Navier--Stokes substitution in the
canonical formal H³ energy derivative.
-/
theorem velocityH3FormalDerivativeAt_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    ) :
    velocityH3FormalDerivativeAt u t
      =
    velocityH3PDEDerivativeAt u p t := by

  unfold
    velocityH3FormalDerivativeAt
    velocityH3PDEDerivativeAt

  rw [
    velocityH3FormalDerivative0At_eq_pde
      s ht,
    velocityH3FormalDerivative1At_eq_pde
      s ht,
    velocityH3FormalDerivative2At_eq_pde
      s ht,
    velocityH3FormalDerivative3At_eq_pde
      s ht
  ]

/--
Combining differentiation under the integral with Navier--Stokes substitution
gives the derivative of the exact canonical H³ energy as the exact PDE pairing.
-/
theorem deriv_velocityH3EnergyAt_eq_pde
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
    {T t : ℝ}
    (
      s :
        PreterminalNavierStokes3
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u
          )
          p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hDerivative :
        H3OrderEnergyDerivativeIdentities
          u t
    ) :
    deriv
        (velocityH3EnergyAt u)
        t
      =
    velocityH3PDEDerivativeAt
      u p t := by

  calc
    deriv
        (velocityH3EnergyAt u)
        t
        =
      velocityH3FormalDerivativeAt
        u t :=
      deriv_velocityH3EnergyAt
        hDerivative

    _ =
      velocityH3PDEDerivativeAt
        u p t :=
      velocityH3FormalDerivativeAt_eq_pde
        s ht

end Euclidean
end Bridge
end PrimeTensor
