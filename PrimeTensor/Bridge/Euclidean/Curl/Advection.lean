import PrimeTensor.Bridge.Euclidean.Curl.Advection.X

/-!
# Curl of advection: remaining components

The x-component of the nonlinear identity is already green.  This file adds
the cyclic y- and z-components.

Before incompressibility:

    curl_y ((u · ∇)u)
      = (u · ∇)ω_y - (ω · ∇)u_y + (div u) ω_y,

    curl_z ((u · ∇)u)
      = (u · ∇)ω_z - (ω · ∇)u_z + (div u) ω_z.

For `VorticitySolution3`, the divergence terms vanish.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Transport of the y-vorticity component by the velocity field. -/
noncomputable def realVorticityTransportY
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  (v t x).component xAxis
      *
    spatial3.d
      xAxis
      (fun y =>
        realVorticityY v t y)
      x
    +
  (
    (v t x).component yAxis
        *
      spatial3.d
        yAxis
        (fun y =>
          realVorticityY v t y)
        x
      +
    (v t x).component zAxis
        *
      spatial3.d
        zAxis
        (fun y =>
          realVorticityY v t y)
        x
  )

/-- Transport of the z-vorticity component by the velocity field. -/
noncomputable def realVorticityTransportZ
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  (v t x).component xAxis
      *
    spatial3.d
      xAxis
      (fun y =>
        realVorticityZ v t y)
      x
    +
  (
    (v t x).component yAxis
        *
      spatial3.d
        yAxis
        (fun y =>
          realVorticityZ v t y)
        x
      +
    (v t x).component zAxis
        *
      spatial3.d
        zAxis
        (fun y =>
          realVorticityZ v t y)
        x
  )

namespace VorticitySolution3

/-- A coordinate derivative of the y-vorticity. -/
theorem spatial_d_realVorticityY
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityY
            s.velocity t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            zAxis
            (fun q =>
              (s.velocity t q).component xAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            xAxis
            (fun q =>
              (s.velocity t q).component zAxis)
        )
        x := by

  have hz :=
    s.velocity_firstPartial_spatialC1
      t xAxis zAxis

  have hx :=
    s.velocity_firstPartial_spatialC1
      t zAxis xAxis

  unfold realVorticityY

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hz hx x a

/-- A coordinate derivative of the z-vorticity. -/
theorem spatial_d_realVorticityZ
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityZ
            s.velocity t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            xAxis
            (fun q =>
              (s.velocity t q).component yAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            yAxis
            (fun q =>
              (s.velocity t q).component xAxis)
        )
        x := by

  have hx :=
    s.velocity_firstPartial_spatialC1
      t yAxis xAxis

  have hy :=
    s.velocity_firstPartial_spatialC1
      t xAxis yAxis

  unfold realVorticityZ

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hx hy x a

/-- Full y-component curl-of-advection identity before incompressibility. -/
theorem curlAdvectionY_with_divergence
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q xAxis)
        x
      -
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q zAxis)
        x
      =
    realVorticityTransportY
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x yAxis
      +
    realDivergence3
        s.velocity t x
      *
    realVorticityY
        s.velocity t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      t x zAxis xAxis,
    s.spatial_d_realAdvectionComponent
      t x xAxis zAxis
  ]

  unfold
    realVorticityTransportY
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityY
      t x xAxis,
    s.spatial_d_realVorticityY
      t x yAxis,
    s.spatial_d_realVorticityY
      t x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      t x xAxis zAxis xAxis,
    s.velocity_spatial_d_comm
      t x xAxis zAxis yAxis,
    s.velocity_spatial_d_comm
      t x zAxis xAxis yAxis,
    s.velocity_spatial_d_comm
      t x zAxis xAxis zAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/-- Incompressible y-component: curl advection = transport - stretching. -/
theorem curlAdvectionY_eq_transport_sub_stretch
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q xAxis)
        x
      -
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q zAxis)
        x
      =
    realVorticityTransportY
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x yAxis := by

  calc
    spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q xAxis)
          x
        -
      spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q zAxis)
          x
      =
      realVorticityTransportY
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x yAxis
        +
      realDivergence3
          s.velocity t x
        *
      realVorticityY
          s.velocity t x :=
      s.curlAdvectionY_with_divergence t x

    _ =
      realVorticityTransportY
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x yAxis := by

      rw [s.realDivergence3_eq_zero t x]
      ring

/-- Full z-component curl-of-advection identity before incompressibility. -/
theorem curlAdvectionZ_with_divergence
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q yAxis)
        x
      -
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q xAxis)
        x
      =
    realVorticityTransportZ
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x zAxis
      +
    realDivergence3
        s.velocity t x
      *
    realVorticityZ
        s.velocity t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      t x xAxis yAxis,
    s.spatial_d_realAdvectionComponent
      t x yAxis xAxis
  ]

  unfold
    realVorticityTransportZ
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityZ
      t x xAxis,
    s.spatial_d_realVorticityZ
      t x yAxis,
    s.spatial_d_realVorticityZ
      t x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      t x yAxis xAxis yAxis,
    s.velocity_spatial_d_comm
      t x yAxis xAxis zAxis,
    s.velocity_spatial_d_comm
      t x xAxis yAxis xAxis,
    s.velocity_spatial_d_comm
      t x xAxis yAxis zAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/-- Incompressible z-component: curl advection = transport - stretching. -/
theorem curlAdvectionZ_eq_transport_sub_stretch
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        xAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q yAxis)
        x
      -
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q xAxis)
        x
      =
    realVorticityTransportZ
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x zAxis := by

  calc
    spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q yAxis)
          x
        -
      spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q xAxis)
          x
      =
      realVorticityTransportZ
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x zAxis
        +
      realDivergence3
          s.velocity t x
        *
      realVorticityZ
          s.velocity t x :=
      s.curlAdvectionZ_with_divergence t x

    _ =
      realVorticityTransportZ
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x zAxis := by

      rw [s.realDivergence3_eq_zero t x]
      ring

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
