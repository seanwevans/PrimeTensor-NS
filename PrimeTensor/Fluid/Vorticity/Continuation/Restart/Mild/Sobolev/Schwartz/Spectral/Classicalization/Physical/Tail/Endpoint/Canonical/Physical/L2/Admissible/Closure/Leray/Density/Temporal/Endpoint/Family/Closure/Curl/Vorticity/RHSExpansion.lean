import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSBridge

/-!
# Algebraic expansion of the endpoint pressure-free vorticity RHS

`RHSBridge` moved the three temporal spatial norm masses onto the explicit
pressure-free vorticity right-hand sides.

The H³ estimates available in `Envelope` and `SquareBound` are stated for
velocity components and their spatial derivatives.  Before applying them, the
RHS therefore needs one last algebraic normalization:

* the diffusion part is written as curl of the componentwise Laplacian;
* the nonlinear part is written as curl of advection;
* one coordinate derivative of advection is expanded by the product rule.

All identities already exist for `PreterminalNavierStokes3`.  This file only
specializes them to the logged old solution carried by
`LoggedPreterminalNavierStokesAdmissible`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable section

/-- One spatial derivative of the old logged advection component, in the exact
product-rule form needed by the endpoint H³ estimate. -/
theorem h3LoggedPreterminal_spatial_d_realAdvectionComponent
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    spatial3.d
        a
        (fun q =>
          realAdvectionComponent
            (logSpaceTimeVectorField u) s q j)
        x
      =
    (
      spatial3.d
          a
          (fun q =>
            (logSpaceTimeVectorField u s q).component xAxis)
          x
        *
      spatial3.d
          xAxis
          (fun q =>
            (logSpaceTimeVectorField u s q).component j)
          x
      +
      (logSpaceTimeVectorField u s x).component xAxis
        *
      spatial3.d
          a
          (spatial3.d
            xAxis
            (fun q =>
              (logSpaceTimeVectorField u s q).component j))
          x
    )
      +
    (
      (
        spatial3.d
            a
            (fun q =>
              (logSpaceTimeVectorField u s q).component yAxis)
            x
          *
        spatial3.d
            yAxis
            (fun q =>
              (logSpaceTimeVectorField u s q).component j)
            x
        +
        (logSpaceTimeVectorField u s x).component yAxis
          *
        spatial3.d
            a
            (spatial3.d
              yAxis
              (fun q =>
                (logSpaceTimeVectorField u s q).component j))
            x
      )
        +
      (
        spatial3.d
            a
            (fun q =>
              (logSpaceTimeVectorField u s q).component zAxis)
            x
          *
        spatial3.d
            zAxis
            (fun q =>
              (logSpaceTimeVectorField u s q).component j)
            x
        +
        (logSpaceTimeVectorField u s x).component zAxis
          *
        spatial3.d
            a
            (spatial3.d
              zAxis
              (fun q =>
                (logSpaceTimeVectorField u s q).component j))
            x
      )
    ) := by
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  exact
    hPDE.spatial_d_realAdvectionComponent
      hs x a j

/-- The pressure-free x-vorticity RHS is curl-Laplacian minus curl-advection. -/
theorem h3LoggedPreterminalVorticityRHSX_eq_curlLaplacian_sub_curlAdvection
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityRHSX u s x
      =
    (
      spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component zAxis))
          x
        -
      spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component yAxis))
          x
    )
      -
    (
      spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q zAxis)
          x
        -
      spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q yAxis)
          x
    ) := by
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hLap :=
    hPDE.curlLaplacianX_eq_laplacianVorticityX
      hs x

  have hAdv :=
    hPDE.curlAdvectionX_eq_transport_sub_stretch
      hs x

  unfold h3LoggedPreterminalVorticityRHSX
  linarith

/-- The pressure-free y-vorticity RHS is curl-Laplacian minus curl-advection. -/
theorem h3LoggedPreterminalVorticityRHSY_eq_curlLaplacian_sub_curlAdvection
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityRHSY u s x
      =
    (
      spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component xAxis))
          x
        -
      spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component zAxis))
          x
    )
      -
    (
      spatial3.d
          zAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q xAxis)
          x
        -
      spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q zAxis)
          x
    ) := by
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hLap :=
    hPDE.curlLaplacianY_eq_laplacianVorticityY
      hs x

  have hAdv :=
    hPDE.curlAdvectionY_eq_transport_sub_stretch
      hs x

  unfold h3LoggedPreterminalVorticityRHSY
  linarith

/-- The pressure-free z-vorticity RHS is curl-Laplacian minus curl-advection. -/
theorem h3LoggedPreterminalVorticityRHSZ_eq_curlLaplacian_sub_curlAdvection
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3) :
    h3LoggedPreterminalVorticityRHSZ u s x
      =
    (
      spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component yAxis))
          x
        -
      spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3
            (fun q =>
              (logSpaceTimeVectorField u s q).component xAxis))
          x
    )
      -
    (
      spatial3.d
          xAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q yAxis)
          x
        -
      spatial3.d
          yAxis
          (fun q =>
            realAdvectionComponent
              (logSpaceTimeVectorField u) s q xAxis)
          x
    ) := by
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hLap :=
    hPDE.curlLaplacianZ_eq_laplacianVorticityZ
      hs x

  have hAdv :=
    hPDE.curlAdvectionZ_eq_transport_sub_stretch
      hs x

  unfold h3LoggedPreterminalVorticityRHSZ
  linarith

end

end Euclidean
end Bridge
end PrimeTensor
