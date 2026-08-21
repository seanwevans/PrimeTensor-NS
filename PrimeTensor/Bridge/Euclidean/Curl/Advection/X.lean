import PrimeTensor.Bridge.Euclidean.Advection.Product

/-!
# Curl of advection: x-component

This file isolates the nonlinear vector-calculus identity behind vortex
stretching.  Before incompressibility, the x-component satisfies

    curl_x ((u · ∇)u)
      = (u · ∇)ω_x - (ω · ∇)u_x + (div u) ω_x.

For a `VorticitySolution3`, `div u = 0`, so this reduces to

    curl_x ((u · ∇)u)
      = (u · ∇)ω_x - (ω · ∇)u_x.

The proof uses only:

* the product-rule expansion from `EuclideanAdvectionProduct`;
* mixed spatial partial commutation;
* finite ring algebra.

The incompressibility hypothesis is consumed only in the final corollary, so
its precise role remains visible.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Explicit classical three-dimensional divergence. -/
noncomputable def realDivergence3
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  spatial3.d
      xAxis
      (fun y =>
        (v t y).component xAxis)
      x
    +
  (
    spatial3.d
        yAxis
        (fun y =>
          (v t y).component yAxis)
        x
      +
    spatial3.d
        zAxis
        (fun y =>
          (v t y).component zAxis)
        x
  )

/-- Transport of the x-vorticity component by the velocity field. -/
noncomputable def realVorticityTransportX
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
        realVorticityX v t y)
      x
    +
  (
    (v t x).component yAxis
        *
      spatial3.d
        yAxis
        (fun y =>
          realVorticityX v t y)
        x
      +
    (v t x).component zAxis
        *
      spatial3.d
        zAxis
        (fun y =>
          realVorticityX v t y)
        x
  )

namespace VorticitySolution3

/-- The explicit divergence vanishes for a vorticity-regular solution. -/
theorem realDivergence3_eq_zero
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    realDivergence3 s.velocity t x = 0 := by

  unfold realDivergence3

  simpa [
    PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity,
    PrimeTensor.Bridge.Euclidean.ClassicalSolution3.velocity
  ] using
    s.solution.incompressible_xyz t x

/--
A coordinate derivative of the x-vorticity is the corresponding difference of
second velocity derivatives.
-/
theorem spatial_d_realVorticityX
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realVorticityX
            s.velocity t q)
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            yAxis
            (fun q =>
              (s.velocity t q).component zAxis)
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            zAxis
            (fun q =>
              (s.velocity t q).component yAxis)
        )
        x := by

  have hy :=
    s.velocity_firstPartial_spatialC1
      t zAxis yAxis

  have hz :=
    s.velocity_firstPartial_spatialC1
      t yAxis zAxis

  unfold realVorticityX

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hy hz x a

/--
The full x-component curl-of-advection identity before imposing
incompressibility.
-/
theorem curlAdvectionX_with_divergence
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q zAxis)
        x
      -
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q yAxis)
        x
      =
    realVorticityTransportX
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x xAxis
      +
    realDivergence3
        s.velocity t x
      *
    realVorticityX
        s.velocity t x := by

  rw [
    s.spatial_d_realAdvectionComponent
      t x yAxis zAxis,
    s.spatial_d_realAdvectionComponent
      t x zAxis yAxis
  ]

  unfold
    realVorticityTransportX
    realVortexStretchComponent
    realDivergence3

  rw [
    s.spatial_d_realVorticityX
      t x xAxis,
    s.spatial_d_realVorticityX
      t x yAxis,
    s.spatial_d_realVorticityX
      t x zAxis
  ]

  rw [
    s.velocity_spatial_d_comm
      t x zAxis yAxis xAxis,
    s.velocity_spatial_d_comm
      t x yAxis zAxis xAxis,
    s.velocity_spatial_d_comm
      t x zAxis yAxis zAxis,
    s.velocity_spatial_d_comm
      t x yAxis zAxis yAxis
  ]

  unfold
    realVorticityX
    realVorticityY
    realVorticityZ

  ring

/--
For incompressible flow, the divergence correction vanishes and the
x-component of curl advection is transport minus vortex stretching.
-/
theorem curlAdvectionX_eq_transport_sub_stretch
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        yAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q zAxis)
        x
      -
    spatial3.d
        zAxis
        (fun q =>
          realAdvectionComponent
            s.velocity t q yAxis)
        x
      =
    realVorticityTransportX
        s.velocity t x
      -
    realVortexStretchComponent
        s.velocity t x xAxis := by

  calc
    spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q zAxis)
          x
        -
      spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              s.velocity t q yAxis)
          x
      =
      realVorticityTransportX
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x xAxis
        +
      realDivergence3
          s.velocity t x
        *
      realVorticityX
          s.velocity t x :=
      s.curlAdvectionX_with_divergence t x

    _ =
      realVorticityTransportX
          s.velocity t x
        -
      realVortexStretchComponent
          s.velocity t x xAxis := by

      rw [s.realDivergence3_eq_zero t x]
      ring

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
