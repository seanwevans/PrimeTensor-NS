import PrimeTensor.Bridge.EuclideanThirdPartials

/-!
# Curl commutes with the Euclidean Laplacian: first component

This module begins the proof of

    curl (Δu) = Δ(curl u)

for a `VorticitySolution3`.

The analysis is factored into reusable scalar lemmas:

* coordinate differentiation is linear across addition/subtraction for `C¹`
  fields;
* a first partial of a `C²` field is `C¹`;
* a pure second partial of a `C³` field is `C¹`;
* the three-dimensional Laplacian expands into its three pure second partials;
* the Laplacian distributes across subtraction for `C²` fields.

The only genuinely third-order step is then supplied by the already-green
`SpatialC3.spatial_d_square_comm`.

This file proves the x-component.  The y/z components are cyclic copies and
will be added only after this analytic core compiles.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeCurlLaplacian
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- Coordinate differentiation is additive on genuinely `C¹` fields. -/
theorem SpatialC1.spatial_d_add
    {dim : Depth}
    {f g : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    (spatial dim).d i
        (fun y => f y + g y)
        x
      =
    (spatial dim).d i f x
      +
    (spatial dim).d i g x := by

  have h :=
    (hf.hasDerivAt_partial x i).add
      (hg.hasDerivAt_partial x i)

  change
    deriv
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
              +
            g (coordinateLine x i t)
        )
        (x i)
      =
    (spatial dim).d i f x
      +
    (spatial dim).d i g x

  exact h.deriv

/-- Coordinate differentiation is subtractive on genuinely `C¹` fields. -/
theorem SpatialC1.spatial_d_sub
    {dim : Depth}
    {f g : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC1 f)
    (hg : SpatialC1 g)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    (spatial dim).d i
        (fun y => f y - g y)
        x
      =
    (spatial dim).d i f x
      -
    (spatial dim).d i g x := by

  have h :=
    (hf.hasDerivAt_partial x i).sub
      (hg.hasDerivAt_partial x i)

  change
    deriv
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
              -
            g (coordinateLine x i t)
        )
        (x i)
      =
    (spatial dim).d i f x
      -
    (spatial dim).d i g x

  exact h.deriv

/-- A first coordinate partial of a `C²` field is `C¹`. -/
theorem SpatialC2.partialDeriv_contDiff_one
    {dim : Depth}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (j : PrimeTensor.Axis dim) :
    SpatialC1
      (
        fun y =>
          partialDeriv j f y
      ) := by

  change
    ContDiff ℝ 1
      (
        fun y =>
          partialDeriv j f y
      )

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_fun_eq
      hf j
  ]

  exact
    (
      PrimeTensor.Bridge.Euclidean.SpatialC2.fderiv_contDiff_one
        hf
    ).clm_apply
      contDiff_const

/-- A pure second coordinate partial of a `C³` field is `C¹`. -/
theorem SpatialC3.secondPartial_contDiff_one
    {dim : Depth}
    {f : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC3 f)
    (i : PrimeTensor.Axis dim) :
    SpatialC1
      (
        (spatial dim).d i
          (
            (spatial dim).d i f
          )
      ) := by

  have hfirst :
      SpatialC2
        (
          fun y =>
            partialDeriv i f y
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
      hf i

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hfirst i

/-- Pure second coordinate differentiation distributes across subtraction. -/
theorem SpatialC2.secondPartial_sub
    {dim : Depth}
    {f g : PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (hg : SpatialC2 g)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    (spatial dim).d i
        (
          (spatial dim).d i
            (fun y => f y - g y)
        )
        x
      =
    (spatial dim).d i
        (
          (spatial dim).d i f
        )
        x
      -
    (spatial dim).d i
        (
          (spatial dim).d i g
        )
        x := by

  have hf1 :
      SpatialC1 f :=
    hf.of_le
      (by norm_num)

  have hg1 :
      SpatialC1 g :=
    hg.of_le
      (by norm_num)

  have hinner :
      (spatial dim).d i
          (fun y => f y - g y)
        =
      fun y =>
        (spatial dim).d i f y
          -
        (spatial dim).d i g y := by

    funext y

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_sub
        hf1 hg1 y i

  rw [hinner]

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_sub
      (
        PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
          hf i
      )
      (
        PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
          hg i
      )
      x i

/-- Explicit three-coordinate expansion of the Euclidean Laplacian. -/
theorem laplacian3_eq
    (f : ScalarField3)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3 f x
      =
    spatial3.d
        xAxis
        (spatial3.d xAxis f)
        x
      +
    (
      spatial3.d
          yAxis
          (spatial3.d yAxis f)
          x
        +
      spatial3.d
          zAxis
          (spatial3.d zAxis f)
          x
    ) := by

  unfold
    PrimeTensor.Bridge.RealFluid.laplacian

  rw [
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ]

/--
The three-dimensional Euclidean Laplacian distributes across subtraction for
spatially `C²` fields.
-/
theorem SpatialC2.laplacian3_sub
    {f g : ScalarField3}
    (hf : SpatialC2 f)
    (hg : SpatialC2 g)
    (x : Point3) :
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y => f y - g y)
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3 f x
      -
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3 g x := by

  rw [
    laplacian3_eq,
    laplacian3_eq,
    laplacian3_eq
  ]

  simp only [spatial3]

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
      hf hg x xAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
      hf hg x yAxis,
    PrimeTensor.Bridge.Euclidean.SpatialC2.secondPartial_sub
      hf hg x zAxis
  ]

  ring

/--
For a spatially `C³` scalar field, one coordinate derivative commutes through
the full three-dimensional Laplacian.
-/
theorem SpatialC3.spatial_d_laplacian3
    {f : ScalarField3}
    (hf : SpatialC3 f)
    (x : Point3)
    (a : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 f
        )
        x
      =
    spatial3.d
        a
        (
          spatial3.d
            xAxis
            (spatial3.d xAxis f)
        )
        x
      +
    (
      spatial3.d
          a
          (
            spatial3.d
              yAxis
              (spatial3.d yAxis f)
          )
          x
        +
      spatial3.d
          a
          (
            spatial3.d
              zAxis
              (spatial3.d zAxis f)
          )
          x
    ) := by

  have hx :
      SpatialC1
        (
          spatial3.d
            xAxis
            (spatial3.d xAxis f)
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf xAxis

  have hy :
      SpatialC1
        (
          spatial3.d
            yAxis
            (spatial3.d yAxis f)
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf yAxis

  have hz :
      SpatialC1
        (
          spatial3.d
            zAxis
            (spatial3.d zAxis f)
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf zAxis

  have hyz :
      SpatialC1
        (
          fun y =>
            spatial3.d
                yAxis
                (spatial3.d yAxis f)
                y
              +
            spatial3.d
                zAxis
                (spatial3.d zAxis f)
                y
        ) :=
    hy.add hz

  have hlap :
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 f
        =
      fun y =>
        spatial3.d
            xAxis
            (spatial3.d xAxis f)
            y
          +
        (
          spatial3.d
              yAxis
              (spatial3.d yAxis f)
              y
            +
          spatial3.d
              zAxis
              (spatial3.d zAxis f)
              y
        ) := by

    funext y

    exact
      laplacian3_eq f y

  rw [hlap]

  simp only [spatial3]
  simp only [spatial3] at hx hy hz hyz

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hx hyz x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial_d_add
      hy hz x a
  ]

namespace VorticitySolution3

/--
The x-component of curl commutes with the Euclidean Laplacian:

    ∂y Δu_z - ∂z Δu_y = Δω_x.
-/
theorem curlLaplacianX_eq_laplacianVorticityX
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component zAxis
            )
        )
        x
      -
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component yAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityX
            s.velocity t y
      )
      x := by

  let uz : ScalarField3 :=
    fun y =>
      (s.velocity t y).component zAxis

  let uy : ScalarField3 :=
    fun y =>
      (s.velocity t y).component yAxis

  have huz3 :
      SpatialC3 uz := by
    simpa [
      uz,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t zAxis

  have huy3 :
      SpatialC3 uy := by
    simpa [
      uy,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t yAxis

  have huz2 :
      SpatialC2 uz :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      huz3

  have huy2 :
      SpatialC2 uy :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.toSpatialC2
      huy3

  have hduz :
      spatial3.d
          yAxis
          (
            PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uz
          )
          x
        =
      spatial3.d yAxis
          (spatial3.d xAxis (spatial3.d xAxis uz)) x
        +
      (
        spatial3.d yAxis
            (spatial3.d yAxis (spatial3.d yAxis uz)) x
          +
        spatial3.d yAxis
            (spatial3.d zAxis (spatial3.d zAxis uz)) x
      ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
      huz3 x yAxis

  have hduy :
      spatial3.d
          zAxis
          (
            PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uy
          )
          x
        =
      spatial3.d zAxis
          (spatial3.d xAxis (spatial3.d xAxis uy)) x
        +
      (
        spatial3.d zAxis
            (spatial3.d yAxis (spatial3.d yAxis uy)) x
          +
        spatial3.d zAxis
            (spatial3.d zAxis (spatial3.d zAxis uy)) x
      ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
      huy3 x zAxis

  have hcomm_uz_x :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huz3 x yAxis xAxis

  have hcomm_uz_y :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huz3 x yAxis yAxis

  have hcomm_uz_z :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huz3 x yAxis zAxis

  have hcomm_uy_x :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huy3 x zAxis xAxis

  have hcomm_uy_y :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huy3 x zAxis yAxis

  have hcomm_uy_z :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      huy3 x zAxis zAxis

  have hlapSub :
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (
            fun y =>
              spatial3.d yAxis uz y
                -
              spatial3.d zAxis uy y
          )
          x
        =
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (spatial3.d yAxis uz)
          x
        -
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (spatial3.d zAxis uy)
          x := by

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.laplacian3_sub
        (
          PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
            huz3 yAxis
        )
        (
          PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
            huy3 zAxis
        )
        x

  change
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz
        )
        x
      -
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d yAxis uz y
            -
          spatial3.d zAxis uy y
      )
      x

  rw [
    hduz,
    hduy,
    hlapSub,
    laplacian3_eq,
    laplacian3_eq
  ]

  simp only [spatial3]

  rw [
    hcomm_uz_x,
    hcomm_uz_y,
    hcomm_uz_z,
    hcomm_uy_x,
    hcomm_uy_y,
    hcomm_uy_z
  ]


end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
