import PrimeTensor.Bridge.EuclideanCurlLaplacian

/-!
# Euclidean product rule and explicit advection derivative

The nonlinear curl calculation repeatedly differentiates products of the form

    u_i ∂ᵢ u_j.

This file isolates that calculus layer.

It adds:

* a genuine coordinate product rule for `SpatialC1`;
* three-dimensional wrappers stated directly with `spatial3`;
* the explicit classical advection component `(u · ∇)u_j`;
* a theorem expanding one spatial derivative of that component.

No vorticity identity is proved here yet.  The purpose is to make the next
curl-of-advection proof finite algebra plus mixed-partial commutation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeAdvectionProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- Coordinate differentiation satisfies the product rule on genuine `C¹` fields. -/
theorem SpatialC1.spatial_d_mul
    {dim : Depth}
    {f g : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    (spatial dim).d i
        (fun y => f y * g y)
        x
      =
    (spatial dim).d i f x * g x
      +
    f x * (spatial dim).d i g x := by

  have h :=
    (hf.hasDerivAt_partial x i).mul
      (hg.hasDerivAt_partial x i)

  change
    deriv
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
              *
            g (coordinateLine x i t)
        )
        (x i)
      =
    (spatial dim).d i f x * g x
      +
    f x * (spatial dim).d i g x

  have hFun :
      (
        fun t : ℝ =>
          f (coordinateLine x i t)
            *
          g (coordinateLine x i t)
      )
        =
      (
        (fun t : ℝ =>
          f (coordinateLine x i t))
          *
        (fun t : ℝ =>
          g (coordinateLine x i t))
      ) := by
    funext t
    rfl

  rw [hFun]

  simpa only [
    coordinateLine_at_base
  ] using
    h.deriv

/-- Three-dimensional wrapper for coordinate additivity. -/
theorem SpatialC1.spatial3_d_add
    {f g : ScalarField3}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (fun y => f y + g y)
        x
      =
    spatial3.d i f x
      +
    spatial3.d i g x := by

  simpa [spatial3] using
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hf hg x i

/-- Three-dimensional wrapper for coordinate subtraction. -/
theorem SpatialC1.spatial3_d_sub
    {f g : ScalarField3}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (fun y => f y - g y)
        x
      =
    spatial3.d i f x
      -
    spatial3.d i g x := by

  simpa [spatial3] using
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_sub
      hf hg x i

/-- Three-dimensional wrapper for the coordinate product rule. -/
theorem SpatialC1.spatial3_d_mul
    {f g : ScalarField3}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (fun y => f y * g y)
        x
      =
    spatial3.d i f x * g x
      +
    f x * spatial3.d i g x := by

  simpa [spatial3] using
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_mul
      hf hg x i

/--
Classical `j`-component of advection `(v · ∇)v`.
-/
noncomputable def realAdvectionComponent
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=

  (v t x).component xAxis *
      spatial3.d
        xAxis
        (fun y =>
          (v t y).component j)
        x
    +
  (
    (v t x).component yAxis *
        spatial3.d
          yAxis
          (fun y =>
            (v t y).component j)
          x
      +
    (v t x).component zAxis *
        spatial3.d
          zAxis
          (fun y =>
            (v t y).component j)
          x
  )

namespace VorticitySolution3

/-- Every fixed-time velocity component is spatially `C¹`. -/
theorem velocity_component_spatialC1
    (s : VorticitySolution3)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        fun y =>
          (s.velocity t y).component j
      ) := by

  have h3 :=
    s.regularity.velocity_spatial_three
      t j

  unfold SpatialC3 at h3
  unfold SpatialC1

  simpa [
    PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
  ] using
    h3.of_le
      (by norm_num)

/-- Every first spatial partial of a velocity component is spatially `C¹`. -/
theorem velocity_firstPartial_spatialC1
    (s : VorticitySolution3)
    (t : ℝ)
    (j i : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        spatial3.d
          i
          (
            fun y =>
              (s.velocity t y).component j
          )
      ) := by

  have h3 :
      SpatialC3
        (
          fun y =>
            (s.velocity t y).component j
        ) := by

    simpa [
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t j

  have h2 :
      SpatialC2
        (
          fun y =>
            partialDeriv i
              (
                fun q =>
                  (s.velocity t q).component j
              )
              y
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      h3 i

  change
    SpatialC1
      (
        fun y =>
          partialDeriv i
            (
              fun q =>
                (s.velocity t q).component j
            )
            y
      )

  exact
    h2.of_le
      (by norm_num)

/--
A fixed-time advection component is spatially `C¹`.
-/
theorem realAdvectionComponent_spatialC1
    (s : VorticitySolution3)
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC1
      (
        fun x =>
          realAdvectionComponent
            s.velocity t x j
      ) := by

  have hux :=
    s.velocity_component_spatialC1
      t xAxis

  have huy :=
    s.velocity_component_spatialC1
      t yAxis

  have huz :=
    s.velocity_component_spatialC1
      t zAxis

  have hdx :=
    s.velocity_firstPartial_spatialC1
      t j xAxis

  have hdy :=
    s.velocity_firstPartial_spatialC1
      t j yAxis

  have hdz :=
    s.velocity_firstPartial_spatialC1
      t j zAxis

  unfold realAdvectionComponent

  exact
    (hux.mul hdx).add
      (
        (huy.mul hdy).add
          (huz.mul hdz)
      )

/--
One spatial derivative of the advection component, fully expanded by the
product rule.
-/
theorem spatial_d_realAdvectionComponent
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          fun q =>
            realAdvectionComponent
              s.velocity t q j
        )
        x
      =
    (
      spatial3.d
          a
          (
            fun q =>
              (s.velocity t q).component xAxis
          )
          x
        *
      spatial3.d
          xAxis
          (
            fun q =>
              (s.velocity t q).component j
          )
          x
      +
      (s.velocity t x).component xAxis
        *
      spatial3.d
          a
          (
            spatial3.d
              xAxis
              (
                fun q =>
                  (s.velocity t q).component j
              )
          )
          x
    )
      +
    (
      (
        spatial3.d
            a
            (
              fun q =>
                (s.velocity t q).component yAxis
            )
            x
          *
        spatial3.d
            yAxis
            (
              fun q =>
                (s.velocity t q).component j
            )
            x
        +
        (s.velocity t x).component yAxis
          *
        spatial3.d
            a
            (
              spatial3.d
                yAxis
                (
                  fun q =>
                    (s.velocity t q).component j
                )
            )
            x
      )
        +
      (
        spatial3.d
            a
            (
              fun q =>
                (s.velocity t q).component zAxis
            )
            x
          *
        spatial3.d
            zAxis
            (
              fun q =>
                (s.velocity t q).component j
            )
            x
        +
        (s.velocity t x).component zAxis
          *
        spatial3.d
            a
            (
              spatial3.d
                zAxis
                (
                  fun q =>
                    (s.velocity t q).component j
                )
            )
            x
      )
    ) := by

  have hux :=
    s.velocity_component_spatialC1
      t xAxis

  have huy :=
    s.velocity_component_spatialC1
      t yAxis

  have huz :=
    s.velocity_component_spatialC1
      t zAxis

  have hdx :=
    s.velocity_firstPartial_spatialC1
      t j xAxis

  have hdy :=
    s.velocity_firstPartial_spatialC1
      t j yAxis

  have hdz :=
    s.velocity_firstPartial_spatialC1
      t j zAxis

  have hpx :
      SpatialC1
        (
          fun q =>
            (s.velocity t q).component xAxis
              *
            spatial3.d
              xAxis
              (
                fun y =>
                  (s.velocity t y).component j
              )
              q
        ) :=
    hux.mul hdx

  have hpy :
      SpatialC1
        (
          fun q =>
            (s.velocity t q).component yAxis
              *
            spatial3.d
              yAxis
              (
                fun y =>
                  (s.velocity t y).component j
              )
              q
        ) :=
    huy.mul hdy

  have hpz :
      SpatialC1
        (
          fun q =>
            (s.velocity t q).component zAxis
              *
            spatial3.d
              zAxis
              (
                fun y =>
                  (s.velocity t y).component j
              )
              q
        ) :=
    huz.mul hdz

  have hpyz :
      SpatialC1
        (
          fun q =>
            (
              (s.velocity t q).component yAxis
                *
              spatial3.d
                yAxis
                (
                  fun y =>
                    (s.velocity t y).component j
                )
                q
            )
              +
            (
              (s.velocity t q).component zAxis
                *
              spatial3.d
                zAxis
                (
                  fun y =>
                    (s.velocity t y).component j
                )
                q
            )
        ) :=
    hpy.add hpz

  unfold realAdvectionComponent

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpx hpyz x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      hux hdx x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_add
      hpy hpz x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huy hdy x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_mul
      huz hdz x a
  ]

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
