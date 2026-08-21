import PrimeTensor.Bridge.Euclidean.Curl.Laplacian.X

/-!
# Curl commutes with the Euclidean Laplacian

The x-component was proved first in `EuclideanCurlLaplacianX`.  This file
factors its analytic core into a generic scalar pair lemma

    ∂ₐ Δf - ∂ᵦ Δg = Δ(∂ₐ f - ∂ᵦ g)

for spatially `C³` scalar fields.  The y- and z-components of
`curl (Δu) = Δ(curl u)` are then immediate cyclic specializations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
For spatially `C³` scalar fields, a difference of coordinate derivatives
commutes through the three-dimensional Euclidean Laplacian.
-/
theorem SpatialC3.curlLaplacianPair
    {f g : ScalarField3}
    (hf : SpatialC3 f)
    (hg : SpatialC3 g)
    (x : Point3)
    (a b : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 f
        )
        x
      -
    spatial3.d
        b
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 g
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d a f y
            -
          spatial3.d b g y
      )
      x := by

  have hdf :
      spatial3.d
          a
          (
            PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 f
          )
          x
        =
      spatial3.d a
          (spatial3.d xAxis (spatial3.d xAxis f)) x
        +
      (
        spatial3.d a
            (spatial3.d yAxis (spatial3.d yAxis f)) x
          +
        spatial3.d a
            (spatial3.d zAxis (spatial3.d zAxis f)) x
      ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
      hf x a

  have hdg :
      spatial3.d
          b
          (
            PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 g
          )
          x
        =
      spatial3.d b
          (spatial3.d xAxis (spatial3.d xAxis g)) x
        +
      (
        spatial3.d b
            (spatial3.d yAxis (spatial3.d yAxis g)) x
          +
        spatial3.d b
            (spatial3.d zAxis (spatial3.d zAxis g)) x
      ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_laplacian3
      hg x b

  have hcomm_f_x :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hf x a xAxis

  have hcomm_f_y :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hf x a yAxis

  have hcomm_f_z :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hf x a zAxis

  have hcomm_g_x :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hg x b xAxis

  have hcomm_g_y :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hg x b yAxis

  have hcomm_g_z :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.spatial_d_square_comm
      hg x b zAxis

  have hlapSub :
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (
            fun y =>
              spatial3.d a f y
                -
              spatial3.d b g y
          )
          x
        =
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (spatial3.d a f)
          x
        -
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (spatial3.d b g)
          x := by

    exact
      PrimeTensor.Bridge.Euclidean.SpatialC2.laplacian3_sub
        (
          PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
            hf a
        )
        (
          PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_contDiff_two
            hg b
        )
        x

  rw [
    hdf,
    hdg,
    hlapSub,
    laplacian3_eq,
    laplacian3_eq
  ]

  simp only [spatial3]

  rw [
    hcomm_f_x,
    hcomm_f_y,
    hcomm_f_z,
    hcomm_g_x,
    hcomm_g_y,
    hcomm_g_z
  ]

namespace VorticitySolution3

/--
The y-component of curl commutes with the Euclidean Laplacian:

    ∂z Δu_x - ∂x Δu_z = Δω_y.
-/
theorem curlLaplacianY_eq_laplacianVorticityY
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component xAxis
            )
        )
        x
      -
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component zAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityY
            s.velocity t y
      )
      x := by

  let ux : ScalarField3 :=
    fun y =>
      (s.velocity t y).component xAxis

  let uz : ScalarField3 :=
    fun y =>
      (s.velocity t y).component zAxis

  have hux3 : SpatialC3 ux := by
    simpa [
      ux,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t xAxis

  have huz3 : SpatialC3 uz := by
    simpa [
      uz,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t zAxis

  change
    spatial3.d
        zAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux
        )
        x
      -
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d zAxis ux y
            -
          spatial3.d xAxis uz y
      )
      x

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.curlLaplacianPair
      hux3 huz3 x zAxis xAxis

/--
The z-component of curl commutes with the Euclidean Laplacian:

    ∂x Δu_y - ∂y Δu_x = Δω_z.
-/
theorem curlLaplacianZ_eq_laplacianVorticityZ
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component yAxis
            )
        )
        x
      -
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (
              fun y =>
                (s.velocity t y).component xAxis
            )
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityZ
            s.velocity t y
      )
      x := by

  let uy : ScalarField3 :=
    fun y =>
      (s.velocity t y).component yAxis

  let ux : ScalarField3 :=
    fun y =>
      (s.velocity t y).component xAxis

  have huy3 : SpatialC3 uy := by
    simpa [
      uy,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t yAxis

  have hux3 : SpatialC3 ux := by
    simpa [
      ux,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t xAxis

  change
    spatial3.d
        xAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy
        )
        x
      -
    spatial3.d
        yAxis
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux
        )
        x
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          spatial3.d xAxis uy y
            -
          spatial3.d yAxis ux y
      )
      x

  exact
    PrimeTensor.Bridge.Euclidean.SpatialC3.curlLaplacianPair
      huy3 hux3 x xAxis yAxis

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
