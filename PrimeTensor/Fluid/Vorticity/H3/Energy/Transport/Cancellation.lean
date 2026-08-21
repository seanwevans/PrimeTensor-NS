import PrimeTensor.Fluid.Vorticity.H3.Energy.Closure

/-!
# Zeroth-order transport cancellation for the H³ energy

The first genuinely nonlinear cancellation in the classical incompressible
energy method is

    ∫ u_j (u · ∇) u_j = 0.

Rather than taking that identity as an assumption, this file proves the
pointwise flux identity

    div (u * u_j^2) = 2 u_j (u · ∇) u_j

from the existing spatial product rule and incompressibility.

The only whole-space analytic input left explicit is that the integral of the
flux divergence vanishes.  This is exactly where decay at spatial infinity (or
an equivalent boundary condition) belongs.

The final theorem specializes the generic real-field cancellation to the
logged velocity and proves that the order-zero contribution to
`velocityH3TransportDerivativeAt` vanishes.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory
open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyTransportCancellation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
The coordinate divergence of the kinetic-energy flux associated with one
velocity component `j`.
-/
noncomputable def transportEnergyFluxDivergenceXYZ
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  spatial3.d
      xAxis
      (
        fun q =>
          (v t q).component xAxis
            *
          (
            (v t q).component j
              *
            (v t q).component j
          )
      )
      x
    +
  (
    spatial3.d
        yAxis
        (
          fun q =>
            (v t q).component yAxis
              *
            (
              (v t q).component j
                *
              (v t q).component j
            )
        )
        x
      +
    spatial3.d
        zAxis
        (
          fun q =>
            (v t q).component zAxis
              *
            (
              (v t q).component j
                *
              (v t q).component j
            )
        )
        x
  )

/--
The only whole-space boundary/decay datum needed for the order-zero transport
cancellation: every componentwise kinetic-energy flux has zero integrated
divergence.
-/
def TransportEnergyFluxVanishesAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ) : Prop :=
  ∀ j : PrimeTensor.Axis Depth.three,
    (
      ∫ x : Point3,
        transportEnergyFluxDivergenceXYZ
          v t j x
    )
      =
    0

/--
For a preterminal incompressible Navier--Stokes field, the divergence of the
componentwise kinetic-energy flux is exactly twice the scalar transport-energy
density.
-/
theorem transportEnergyFluxDivergenceXYZ_eq_two_mul_advection
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
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
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    transportEnergyFluxDivergenceXYZ
        v t j x
      =
    2
      * (v t x).component j
      * realAdvectionComponent
          v t x j := by

  have hux :
      SpatialC1
        (
          fun q =>
            (v t q).component xAxis
        ) :=
    s.velocity_component_spatialC1
      ht xAxis

  have huy :
      SpatialC1
        (
          fun q =>
            (v t q).component yAxis
        ) :=
    s.velocity_component_spatialC1
      ht yAxis

  have huz :
      SpatialC1
        (
          fun q =>
            (v t q).component zAxis
        ) :=
    s.velocity_component_spatialC1
      ht zAxis

  have hfj :
      SpatialC1
        (
          fun q =>
            (v t q).component j
        ) :=
    s.velocity_component_spatialC1
      ht j

  have hfj2 :
      SpatialC1
        (
          fun q =>
            (v t q).component j
              *
            (v t q).component j
        ) :=
    hfj.mul hfj

  have hDiv :
      spatial3.d
          xAxis
          (
            fun q =>
              (v t q).component xAxis
          )
          x
        +
      (
        spatial3.d
            yAxis
            (
              fun q =>
                (v t q).component yAxis
            )
            x
          +
        spatial3.d
            zAxis
            (
              fun q =>
                (v t q).component zAxis
            )
            x
      )
        =
      0 :=
    s.incompressible_xyz
      ht x

  unfold transportEnergyFluxDivergenceXYZ

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hux hfj2 x xAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huy hfj2 x yAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huz hfj2 x zAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hfj hfj x xAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hfj hfj x yAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hfj hfj x zAxis
  ]

  unfold realAdvectionComponent

  nlinarith [hDiv]

/--
The whole-space flux condition turns the pointwise divergence identity into
the standard order-zero incompressible transport cancellation.
-/
theorem spatialEnergyPairing_advection_eq_zero
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
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
          v p T
    )
    (
      ht :
        t ∈ Set.Ioo (0 : ℝ) T
    )
    (
      hFlux :
        TransportEnergyFluxVanishesAt
          v t
    )
    (j : PrimeTensor.Axis Depth.three) :
    spatialEnergyPairing
        (
          fun x =>
            (v t x).component j
        )
        (
          fun x =>
            realAdvectionComponent
              v t x j
        )
      =
    0 := by

  have hPointwise :
      (
        fun x : Point3 =>
          transportEnergyFluxDivergenceXYZ
            v t j x
      )
        =
      (
        fun x : Point3 =>
          2
            *
          (
            (v t x).component j
              *
            realAdvectionComponent
              v t x j
          )
      ) := by

    funext x

    simpa [mul_assoc] using
      transportEnergyFluxDivergenceXYZ_eq_two_mul_advection
        s ht j x

  have hIntegral :
      (
        ∫ x : Point3,
          2
            *
          (
            (v t x).component j
              *
            realAdvectionComponent
              v t x j
          )
      )
        =
      0 := by

    rw [
      ← hPointwise
    ]

    exact
      hFlux j

  unfold spatialEnergyPairing

  rw [
    ← MeasureTheory.integral_const_mul
  ]

  exact hIntegral

/--
Logged specialization of the whole-space order-zero transport flux condition.
-/
def H3TransportEnergyFluxVanishesAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ) : Prop :=
  TransportEnergyFluxVanishesAt
    (
      PrimeTensor.Bridge.logSpaceTimeVectorField
        u
    )
    t

/--
The zeroth-order transport contribution to the canonical H³ derivative
vanishes for an energy-class solution under the explicit whole-space
kinetic-energy flux condition.
-/
theorem velocityH3TransportDerivative0At_eq_zero_of_energyClass
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
    )
    (
      hFlux :
        H3TransportEnergyFluxVanishesAt
          u t
    ) :
    velocityH3TransportDerivative0At
        u t
      =
    0 := by

  rcases hClass.pressure_witness with
    ⟨
      p,
      s,
      hp4
    ⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  unfold velocityH3TransportDerivative0At

  apply Finset.sum_eq_zero

  intro j hj

  change
    spatialEnergyPairing
        (
          fun x =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t x
            ).component j
        )
        (
          fun x =>
            realAdvectionComponent
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t x j
        )
      =
    0

  exact
    spatialEnergyPairing_advection_eq_zero
      s
      htNS
      hFlux
      j

end Euclidean
end Bridge
end PrimeTensor
