import PrimeTensor.Fluid.Vorticity.H3.Axis.Sum

/-!
# Differentiated incompressibility for the H³ energy class

The H³ pressure cancellation package asks for pointwise divergence-freeness
after zero through three common spatial derivatives.  This file derives that
property from the preterminal Navier--Stokes incompressibility equation and the
high-order spatial regularity already stored in `PreterminalH3EnergyClass`.

The proof is deliberately three-dimensional and explicit:

* use the `x/y/z` incompressibility equation;
* differentiate the explicit `x + (y + z)` field;
* distribute the derivative using the genuine `C¹` linearity lemmas;
* commute the newly introduced derivative past the component derivative;
* use `axis_sum_three` only at the final finite-sum boundary.

No integration-by-parts or decay assumption is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open scoped BigOperators

noncomputable local instance axisFintypeH3EnergyDivergence
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Small regularity helpers -/

/-- A spatial derivative of the zero field is zero. -/
private theorem spatial3_d_zero
    (i : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    spatial3.d
        i
        (fun _ : Point3 => (0 : ℝ))
        x
      =
    0 := by

  apply
    PrimeTensor.Bridge.Euclidean.spatial_d_eq_of_hasDerivAt

  simpa using
    (hasDerivAt_const (x i) (0 : ℝ))

/-- Logged velocity components inherit the preterminal `C³` spatial regularity. -/
private theorem loggedVelocityComponent_spatialC3
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
    SpatialC3
      (loggedVelocityComponent u t j) := by

  change
    SpatialC3
      (
        fun x : Point3 =>
          (
            PrimeTensor.Bridge.logSpaceTimeVectorField
              u t x
          ).component j
      )

  exact
    s.regularity.velocity_spatial_three
      t ht j

/-- First partials of logged velocity components are spatially `C¹`. -/
private theorem loggedVelocityFirstPartial_spatialC1
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
    (j i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d i
          (loggedVelocityComponent u t j)
      ) := by

  change
    SpatialC1
      (
        spatial3.d i
          (
            fun y : Point3 =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t y
              ).component j
          )
      )

  exact
    s.velocity_firstPartial_spatialC1
      ht j i

/-- First partials of a preterminal `C³` velocity component are `C²`. -/
private theorem loggedVelocityFirstPartial_spatialC2
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
    (j i : PrimeTensor.Axis Depth.three) :
    SpatialC2
      (
        spatial3.d i
          (loggedVelocityComponent u t j)
      ) := by

  have h3 :
      SpatialC3
        (loggedVelocityComponent u t j) :=
    loggedVelocityComponent_spatialC3
      s ht j

  change
    SpatialC2
      (
        fun y =>
          partialDeriv i
            (loggedVelocityComponent u t j)
            y
      )

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h3 i

/-- Mixed second partials of a preterminal velocity component are `C¹`. -/
private theorem loggedVelocitySecondPartial_spatialC1
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
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d i
          (
            spatial3.d k
              (loggedVelocityComponent u t j)
          )
      ) := by

  have h2 :
      SpatialC2
        (
          spatial3.d k
            (loggedVelocityComponent u t j)
        ) :=
    loggedVelocityFirstPartial_spatialC2
      s ht j k

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      h2 i

/-- The H⁵ justification class supplies `C³` regularity of every second partial. -/
private theorem loggedVelocitySecondPartial_spatialC3_of_H5
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T t : ℝ}
    (
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      ht :
        t ∈ Set.Ico a T
    )
    (j i k : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (
        spatial3.d i
          (
            spatial3.d k
              (loggedVelocityComponent u t j)
          )
      ) := by

  change
    SpatialC3
      (
        spatial3.d i
          (
            spatial3.d k
              (
                fun x : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t x
                  ).component j
              )
          )
      )

  exact
    h5 t ht j i k

/-- A first derivative of a `C³` scalar field is at least `C¹`. -/
private theorem firstPartial_spatialC1_of_spatialC3
    {f : ScalarField3}
    (
      h :
        SpatialC3 f
    )
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (spatial3.d i f) := by

  have h2 :
      SpatialC2
        (
          fun y =>
            partialDeriv i f y
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h i

  change
    SpatialC1
      (
        fun y =>
          partialDeriv i f y
      )

  exact
    h2.of_le
      (by norm_num)

/-! ## Explicit differentiated divergence identities -/

/-- Zeroth-order incompressibility in explicit three-axis form. -/
private theorem divergenceXYZ0_eq_zero
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
    (x : Point3) :
    spatial3.d
          xAxis
          (loggedVelocityComponent u t xAxis)
          x
      +
      (
        spatial3.d
            yAxis
            (loggedVelocityComponent u t yAxis)
            x
          +
        spatial3.d
            zAxis
            (loggedVelocityComponent u t zAxis)
            x
      )
      =
    0 := by

  change
    spatial3.d
          xAxis
          (
            fun y : Point3 =>
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u t y
              ).component xAxis
          )
          x
      +
      (
        spatial3.d
            yAxis
            (
              fun y : Point3 =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component yAxis
            )
            x
          +
        spatial3.d
            zAxis
            (
              fun y : Point3 =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component zAxis
            )
            x
      )
      =
    0

  exact
    s.incompressible_xyz
      ht x

/--
One common spatial derivative of incompressibility, with the component
derivative restored to the outside by mixed-partial commutation.
-/
private theorem divergenceXYZ1_eq_zero
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
    (i : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    spatial3.d
          xAxis
          (
            spatial3.d i
              (loggedVelocityComponent u t xAxis)
          )
          x
      +
      (
        spatial3.d
            yAxis
            (
              spatial3.d i
                (loggedVelocityComponent u t yAxis)
            )
            x
          +
        spatial3.d
            zAxis
            (
              spatial3.d i
                (loggedVelocityComponent u t zAxis)
            )
            x
      )
      =
    0 := by

  have hx :
      SpatialC1
        (
          spatial3.d xAxis
            (loggedVelocityComponent u t xAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC1
      s ht xAxis xAxis

  have hy :
      SpatialC1
        (
          spatial3.d yAxis
            (loggedVelocityComponent u t yAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC1
      s ht yAxis yAxis

  have hz :
      SpatialC1
        (
          spatial3.d zAxis
            (loggedVelocityComponent u t zAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC1
      s ht zAxis zAxis

  have hyz :
      SpatialC1
        (
          fun q =>
            spatial3.d yAxis
                (loggedVelocityComponent u t yAxis)
                q
              +
            spatial3.d zAxis
                (loggedVelocityComponent u t zAxis)
                q
        ) :=
    hy.add hz

  have hField :
      (
        fun q : Point3 =>
          spatial3.d xAxis
              (loggedVelocityComponent u t xAxis)
              q
            +
          (
            spatial3.d yAxis
                (loggedVelocityComponent u t yAxis)
                q
              +
            spatial3.d zAxis
                (loggedVelocityComponent u t zAxis)
                q
          )
      )
        =
      fun _ : Point3 => (0 : ℝ) := by

    funext q
    exact
      divergenceXYZ0_eq_zero
        s ht q

  have hDeriv :=
    congrFun
      (
        congrArg
          (spatial3.d i)
          hField
      )
      x

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hx hyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hy hz x i,
    spatial3_d_zero
  ] at hDeriv

  have hcx :
      spatial3.d i
          (
            spatial3.d xAxis
              (loggedVelocityComponent u t xAxis)
          )
          x
        =
      spatial3.d xAxis
          (
            spatial3.d i
              (loggedVelocityComponent u t xAxis)
          )
          x := by

    change
      spatial3.d i
          (
            spatial3.d xAxis
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
          )
          x
        =
      spatial3.d xAxis
          (
            spatial3.d i
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
          )
          x

    exact
      s.velocity_spatial_d_comm
        ht x xAxis i xAxis

  have hcy :
      spatial3.d i
          (
            spatial3.d yAxis
              (loggedVelocityComponent u t yAxis)
          )
          x
        =
      spatial3.d yAxis
          (
            spatial3.d i
              (loggedVelocityComponent u t yAxis)
          )
          x := by

    change
      spatial3.d i
          (
            spatial3.d yAxis
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
          )
          x
        =
      spatial3.d yAxis
          (
            spatial3.d i
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
          )
          x

    exact
      s.velocity_spatial_d_comm
        ht x yAxis i yAxis

  have hcz :
      spatial3.d i
          (
            spatial3.d zAxis
              (loggedVelocityComponent u t zAxis)
          )
          x
        =
      spatial3.d zAxis
          (
            spatial3.d i
              (loggedVelocityComponent u t zAxis)
          )
          x := by

    change
      spatial3.d i
          (
            spatial3.d zAxis
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
          )
          x
        =
      spatial3.d zAxis
          (
            spatial3.d i
              (
                fun y : Point3 =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
          )
          x

    exact
      s.velocity_spatial_d_comm
        ht x zAxis i zAxis

  rw [hcx, hcy, hcz] at hDeriv

  exact hDeriv

/-- Two common spatial derivatives of incompressibility. -/
private theorem divergenceXYZ2_eq_zero
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
    (i k : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    spatial3.d
          xAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t xAxis)
              )
          )
          x
      +
      (
        spatial3.d
            yAxis
            (
              spatial3.d i
                (
                  spatial3.d k
                    (loggedVelocityComponent u t yAxis)
                )
            )
            x
          +
        spatial3.d
            zAxis
            (
              spatial3.d i
                (
                  spatial3.d k
                    (loggedVelocityComponent u t zAxis)
                )
            )
            x
      )
      =
    0 := by

  have hx :
      SpatialC1
        (
          spatial3.d xAxis
            (
              spatial3.d k
                (loggedVelocityComponent u t xAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC1
      s ht xAxis xAxis k

  have hy :
      SpatialC1
        (
          spatial3.d yAxis
            (
              spatial3.d k
                (loggedVelocityComponent u t yAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC1
      s ht yAxis yAxis k

  have hz :
      SpatialC1
        (
          spatial3.d zAxis
            (
              spatial3.d k
                (loggedVelocityComponent u t zAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC1
      s ht zAxis zAxis k

  have hyz :
      SpatialC1
        (
          fun q =>
            spatial3.d yAxis
                (
                  spatial3.d k
                    (loggedVelocityComponent u t yAxis)
                )
                q
              +
            spatial3.d zAxis
                (
                  spatial3.d k
                    (loggedVelocityComponent u t zAxis)
                )
                q
        ) :=
    hy.add hz

  have hField :
      (
        fun q : Point3 =>
          spatial3.d xAxis
              (
                spatial3.d k
                  (loggedVelocityComponent u t xAxis)
              )
              q
            +
          (
            spatial3.d yAxis
                (
                  spatial3.d k
                    (loggedVelocityComponent u t yAxis)
                )
                q
              +
            spatial3.d zAxis
                (
                  spatial3.d k
                    (loggedVelocityComponent u t zAxis)
                )
                q
          )
      )
        =
      fun _ : Point3 => (0 : ℝ) := by

    funext q
    exact
      divergenceXYZ1_eq_zero
        s ht k q

  have hDeriv :=
    congrFun
      (
        congrArg
          (spatial3.d i)
          hField
      )
      x

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hx hyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hy hz x i,
    spatial3_d_zero
  ] at hDeriv

  have h2x :
      SpatialC2
        (
          spatial3.d k
            (loggedVelocityComponent u t xAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC2
      s ht xAxis k

  have h2y :
      SpatialC2
        (
          spatial3.d k
            (loggedVelocityComponent u t yAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC2
      s ht yAxis k

  have h2z :
      SpatialC2
        (
          spatial3.d k
            (loggedVelocityComponent u t zAxis)
        ) :=
    loggedVelocityFirstPartial_spatialC2
      s ht zAxis k

  have hcx :
      spatial3.d i
          (
            spatial3.d xAxis
              (
                spatial3.d k
                  (loggedVelocityComponent u t xAxis)
              )
          )
          x
        =
      spatial3.d xAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t xAxis)
              )
          )
          x := by

    simpa only [spatial3] using
      h2x.spatial_d_comm
        x i xAxis

  have hcy :
      spatial3.d i
          (
            spatial3.d yAxis
              (
                spatial3.d k
                  (loggedVelocityComponent u t yAxis)
              )
          )
          x
        =
      spatial3.d yAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t yAxis)
              )
          )
          x := by

    simpa only [spatial3] using
      h2y.spatial_d_comm
        x i yAxis

  have hcz :
      spatial3.d i
          (
            spatial3.d zAxis
              (
                spatial3.d k
                  (loggedVelocityComponent u t zAxis)
              )
          )
          x
        =
      spatial3.d zAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (loggedVelocityComponent u t zAxis)
              )
          )
          x := by

    simpa only [spatial3] using
      h2z.spatial_d_comm
        x i zAxis

  rw [hcx, hcy, hcz] at hDeriv

  exact hDeriv

/-- Three common spatial derivatives of incompressibility. -/
private theorem divergenceXYZ3_eq_zero
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
      h5 :
        VelocitySpatialC5OnTail
          u a T
    )
    (
      htTail :
        t ∈ Set.Ico a T
    )
    (i k l : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    spatial3.d
          xAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t xAxis)
                  )
              )
          )
          x
      +
      (
        spatial3.d
            yAxis
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t yAxis)
                    )
                )
            )
            x
          +
        spatial3.d
            zAxis
            (
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t zAxis)
                    )
                )
            )
            x
      )
      =
    0 := by

  have h3x :
      SpatialC3
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t xAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC3_of_H5
      h5 htTail xAxis k l

  have h3y :
      SpatialC3
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t yAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC3_of_H5
      h5 htTail yAxis k l

  have h3z :
      SpatialC3
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t zAxis)
            )
        ) :=
    loggedVelocitySecondPartial_spatialC3_of_H5
      h5 htTail zAxis k l

  have hx :
      SpatialC1
        (
          spatial3.d xAxis
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t xAxis)
                )
            )
        ) :=
    firstPartial_spatialC1_of_spatialC3
      h3x xAxis

  have hy :
      SpatialC1
        (
          spatial3.d yAxis
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t yAxis)
                )
            )
        ) :=
    firstPartial_spatialC1_of_spatialC3
      h3y yAxis

  have hz :
      SpatialC1
        (
          spatial3.d zAxis
            (
              spatial3.d k
                (
                  spatial3.d l
                    (loggedVelocityComponent u t zAxis)
                )
            )
        ) :=
    firstPartial_spatialC1_of_spatialC3
      h3z zAxis

  have hyz :
      SpatialC1
        (
          fun q =>
            spatial3.d yAxis
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t yAxis)
                    )
                )
                q
              +
            spatial3.d zAxis
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t zAxis)
                    )
                )
                q
        ) :=
    hy.add hz

  have hField :
      (
        fun q : Point3 =>
          spatial3.d xAxis
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t xAxis)
                  )
              )
              q
            +
          (
            spatial3.d yAxis
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t yAxis)
                    )
                )
                q
              +
            spatial3.d zAxis
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t zAxis)
                    )
                )
                q
          )
      )
        =
      fun _ : Point3 => (0 : ℝ) := by

    funext q
    exact
      divergenceXYZ2_eq_zero
        s ht k l q

  have hDeriv :=
    congrFun
      (
        congrArg
          (spatial3.d i)
          hField
      )
      x

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hx hyz x i,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hy hz x i,
    spatial3_d_zero
  ] at hDeriv

  have h2x :
      SpatialC2
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t xAxis)
            )
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      h3x

  have h2y :
      SpatialC2
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t yAxis)
            )
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      h3y

  have h2z :
      SpatialC2
        (
          spatial3.d k
            (
              spatial3.d l
                (loggedVelocityComponent u t zAxis)
            )
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      h3z

  have hcx :
      spatial3.d i
          (
            spatial3.d xAxis
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t xAxis)
                  )
              )
          )
          x
        =
      spatial3.d xAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t xAxis)
                  )
              )
          )
          x := by

    simpa only [spatial3] using
      h2x.spatial_d_comm
        x i xAxis

  have hcy :
      spatial3.d i
          (
            spatial3.d yAxis
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t yAxis)
                  )
              )
          )
          x
        =
      spatial3.d yAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t yAxis)
                  )
              )
          )
          x := by

    simpa only [spatial3] using
      h2y.spatial_d_comm
        x i yAxis

  have hcz :
      spatial3.d i
          (
            spatial3.d zAxis
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t zAxis)
                  )
              )
          )
          x
        =
      spatial3.d zAxis
          (
            spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t zAxis)
                  )
              )
          )
          x := by

    simpa only [spatial3] using
      h2z.spatial_d_comm
        x i zAxis

  rw [hcx, hcy, hcz] at hDeriv

  exact hDeriv

/-! ## H³ pressure-family result -/

/--
Every preterminal H³ energy-class state is divergence-free after zero through
three common spatial derivatives at every strict tail time.
-/
theorem preterminalH3EnergyClass_produces_differentiatedIncompressibility
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
    H3DifferentiatedIncompressibilityAt
      u t := by

  classical

  rcases
      hClass.pressure_witness
    with
      ⟨p, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T := by
    exact
      ⟨
        lt_trans
          hClass.terminal_start.1
          ht.1,
        ht.2
      ⟩

  have htTail :
      t ∈ Set.Ico a T := by
    exact
      ⟨
        le_of_lt ht.1,
        ht.2
      ⟩

  unfold H3DifferentiatedIncompressibilityAt

  refine
    ⟨
      ?_,
      ?_
    ⟩

  · unfold DifferentiatedDivergenceFree
    intro x

    rw [axis_sum_three]

    simpa [h3PressureVelocityFamily0] using
      divergenceXYZ0_eq_zero
        s htNS x

  · refine
      ⟨
        ?_,
        ?_
      ⟩

    · intro i

      unfold DifferentiatedDivergenceFree
      intro x

      rw [axis_sum_three]

      simpa [h3PressureVelocityFamily1] using
        divergenceXYZ1_eq_zero
          s htNS i x

    · refine
        ⟨
          ?_,
          ?_
        ⟩

      · intro i k

        unfold DifferentiatedDivergenceFree
        intro x

        rw [axis_sum_three]

        simpa [h3PressureVelocityFamily2] using
          divergenceXYZ2_eq_zero
            s htNS i k x

      · intro i k l

        unfold DifferentiatedDivergenceFree
        intro x

        rw [axis_sum_three]

        simpa [h3PressureVelocityFamily3] using
          divergenceXYZ3_eq_zero
            s
            htNS
            hClass.velocity_spatial_five
            htTail
            i k l x

end Euclidean
end Bridge
end PrimeTensor
