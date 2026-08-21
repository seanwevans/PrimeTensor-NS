import PrimeTensor.Bridge.Euclidean.Curl.Advection

/-!
# Classical vorticity equation: x-component

All analytic ingredients are already available.  This file first rearranges
the explicit momentum equation into

    ∂ₜ u_j = Δu_j - (u · ∇)u_j - ∂ⱼp,

then differentiates that *function equality* spatially.  This is important:
we do not need to assume independently that the field `∂ₜ u_j` is spatially
`C¹`.  The right-hand side has all required regularity, and equality of
functions lets the total spatial derivative be rewritten onto that side.

The x-vorticity equation then follows by combining four already-green facts:

* time derivative commutes with curl;
* curl advection = transport - stretching;
* curl grad pressure = 0;
* curl Laplacian = Laplacian curl.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeVorticityEquation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- A three-dimensional Laplacian of a spatially `C³` scalar field is `C¹`. -/
theorem SpatialC3.laplacian3_spatialC1
    {f : ScalarField3}
    (hf : SpatialC3 f) :
    SpatialC1
      (
        PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 f
      ) := by

  have hx :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf xAxis

  have hy :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf yAxis

  have hz :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.secondPartial_contDiff_one
      hf zAxis

  have hsum :
      SpatialC1
        (
          fun x =>
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
            )
        ) :=
    hx.add (hy.add hz)

  have hlap :
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 f
        =
      fun x =>
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

    funext x
    exact laplacian3_eq f x

  rw [hlap]

  exact hsum

namespace VorticitySolution3

/--
The explicit momentum equation rearranged pointwise as

    ∂ₜu_j = Δu_j - advection_j - ∂ⱼp.
-/
theorem temporalComponent_eq_laplacian_sub_advection_sub_pressure
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    temporal.d
        (fun τ =>
          (s.velocity τ x).component j)
        t
      =
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          (s.velocity t y).component j)
        x
      -
    realAdvectionComponent
        s.velocity t x j
      -
    spatial3.d
        j
        (s.pressure t)
        x := by

  have h :=
    s.solution.momentum_xyz
      t x j

  rw [
    laplacian3_eq
  ]

  unfold realAdvectionComponent

  simp only [
    PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity,
    PrimeTensor.Bridge.Euclidean.VorticitySolution3.pressure
  ]

  linarith

/--
A spatial derivative of the temporal velocity component can therefore be
computed entirely from the spatially regular right-hand side of momentum.
-/
theorem spatial_d_temporalComponent
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (
          fun q =>
            temporal.d
              (fun τ =>
                (s.velocity τ q).component j)
              t
        )
        x
      =
    spatial3.d
        a
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (s.velocity t q).component j)
        )
        x
      -
    spatial3.d
        a
        (
          fun q =>
            realAdvectionComponent
              s.velocity t q j
        )
        x
      -
    spatial3.d
        a
        (
          spatial3.d
            j
            (s.pressure t)
        )
        x := by

  let uj : ScalarField3 :=
    fun q =>
      (s.velocity t q).component j

  have huj3 :
      SpatialC3 uj := by

    simpa [
      uj,
      PrimeTensor.Bridge.Euclidean.VorticitySolution3.velocity
    ] using
      s.regularity.velocity_spatial_three
        t j

  have hlap :
      SpatialC1
        (
          PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uj
        ) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huj3

  have hadv :
      SpatialC1
        (
          fun q =>
            realAdvectionComponent
              s.velocity t q j
        ) :=
    s.realAdvectionComponent_spatialC1
      t j

  have hp :
      SpatialC1
        (
          spatial3.d
            j
            (s.pressure t)
        ) := by

    have hp2 :=
      s.regularity.pressure_spatial_two
        t

    have h :=
      PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
        hp2 j

    change
      SpatialC1
        (
          fun y =>
            partialDeriv j
              (s.pressure t)
              y
        )

    exact h

  have hfun :
      (
        fun q =>
          temporal.d
            (fun τ =>
              (s.velocity τ q).component j)
            t
      )
        =
      (
        fun q =>
          PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj q
            -
          realAdvectionComponent
              s.velocity t q j
            -
          spatial3.d
              j
              (s.pressure t)
              q
      ) := by

    funext q

    simpa [uj] using
      s.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        t q j

  rw [hfun]

  have hlapAdv :
      SpatialC1
        (
          fun q =>
            PrimeTensor.Bridge.RealFluid.laplacian
                spatial3 uj q
              -
            realAdvectionComponent
                s.velocity t q j
        ) :=
    hlap.sub hadv

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hlapAdv hp x a,
    PrimeTensor.Bridge.Euclidean.SpatialC1.spatial3_d_sub
      hlap hadv x a
  ]

/--
The x-component of the normalized three-dimensional incompressible vorticity
equation:

    ∂ₜωₓ + (u · ∇)ωₓ = (ω · ∇)uₓ + Δωₓ.
-/
theorem vorticityEquationX
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityX
            s.velocity τ x)
        t
      +
    realVorticityTransportX
        s.velocity t x
      =
    realVortexStretchComponent
        s.velocity t x xAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityX
            s.velocity t y)
        x := by

  rw [
    s.temporal_realVorticityX
      t x,
    s.spatial_d_temporalComponent
      t x yAxis zAxis,
    s.spatial_d_temporalComponent
      t x zAxis yAxis
  ]

  have hAdv :=
    s.curlAdvectionX_eq_transport_sub_stretch
      t x

  have hPressure :=
    s.pressureCurlX_eq_zero
      t x

  have hLaplacian :=
    s.curlLaplacianX_eq_laplacianVorticityX
      t x

  linarith

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
