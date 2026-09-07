import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge

/-!
# Spatial continuity of the pressure-free preterminal vorticity RHS

`Curl.Vorticity.Derivative` proved that, at every fixed spatial point, the
classical vorticity trajectories have genuine time derivatives equal to the
pressure-free vorticity RHS.

This file proves the complementary sectionwise fact: at every strict
preterminal time, each of those three RHS components is continuous in space.

Rather than expanding transport and stretching into products, we use the
already-proved vector-calculus identities

    curl(Δu) = Δ(curl u),
    curl((u · ∇)u) = transport - stretch.

Hence the pressure-free vorticity RHS is simply

    curl(Δu) - curl((u · ∇)u).

Each velocity component is spatially `C³`, so its Laplacian is `C¹`.
Each advection component is already `C¹`.  Therefore the first spatial
derivatives appearing in both curls are continuous.

No temporal continuity of pressure is used, and no joint spacetime continuity
is asserted.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped Topology

noncomputable section

/-- The x-component pressure-free vorticity RHS is continuous in space at each
strict preterminal time. -/
theorem h3LoggedPreterminalVorticityRHSX_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (h3LoggedPreterminalVorticityRHSX u s) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let uz : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component zAxis

  let uy : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component yAxis

  have huz3 : SpatialC3 uz := by
    simpa [uz] using
      hPDE.regularity.velocity_spatial_three
        s hs zAxis

  have huy3 : SpatialC3 uy := by
    simpa [uy] using
      hPDE.regularity.velocity_spatial_three
        s hs yAxis

  have hLapZ :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uz) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huz3

  have hLapY :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uy) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huy3

  have hAdvZ :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x zAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs zAxis

  have hAdvY :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x yAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs yAxis

  have hLapZDeriv :
      Continuous
        (spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapZ yAxis

  have hLapYDeriv :
      Continuous
        (spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapY zAxis

  have hAdvZDeriv :
      Continuous
        (spatial3.d
          yAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x zAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvZ yAxis

  have hAdvYDeriv :
      Continuous
        (spatial3.d
          zAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x yAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvY zAxis

  have hEq :
      h3LoggedPreterminalVorticityRHSX u s
        =
      fun x : Point3 =>
        (spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uz)
            x
          -
         spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uy)
            x)
          -
        (spatial3.d
            yAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q zAxis)
            x
          -
         spatial3.d
            zAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q yAxis)
            x) := by
    funext x

    have hLap :=
      hPDE.curlLaplacianX_eq_laplacianVorticityX
        hs x

    have hLap' :
        spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uz)
            x
          -
        spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uy)
            x
          =
        PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (fun y : Point3 =>
            realVorticityX
              (logSpaceTimeVectorField u) s y)
          x := by
      simpa [uz, uy] using hLap

    have hAdv :=
      hPDE.curlAdvectionX_eq_transport_sub_stretch
        hs x

    unfold h3LoggedPreterminalVorticityRHSX
    linarith [hLap', hAdv]
  rw [hEq]
  exact
    (hLapZDeriv.sub hLapYDeriv).sub
      (hAdvZDeriv.sub hAdvYDeriv)

/-- The y-component pressure-free vorticity RHS is continuous in space at each
strict preterminal time. -/
theorem h3LoggedPreterminalVorticityRHSY_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (h3LoggedPreterminalVorticityRHSY u s) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let ux : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component xAxis

  let uz : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component zAxis

  have hux3 : SpatialC3 ux := by
    simpa [ux] using
      hPDE.regularity.velocity_spatial_three
        s hs xAxis

  have huz3 : SpatialC3 uz := by
    simpa [uz] using
      hPDE.regularity.velocity_spatial_three
        s hs zAxis

  have hLapX :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 ux) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      hux3

  have hLapZ :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uz) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huz3

  have hAdvX :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x xAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs xAxis

  have hAdvZ :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x zAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs zAxis

  have hLapXDeriv :
      Continuous
        (spatial3.d
          zAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapX zAxis

  have hLapZDeriv :
      Continuous
        (spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uz)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapZ xAxis

  have hAdvXDeriv :
      Continuous
        (spatial3.d
          zAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x xAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvX zAxis

  have hAdvZDeriv :
      Continuous
        (spatial3.d
          xAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x zAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvZ xAxis

  have hEq :
      h3LoggedPreterminalVorticityRHSY u s
        =
      fun x : Point3 =>
        (spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 ux)
            x
          -
         spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uz)
            x)
          -
        (spatial3.d
            zAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q xAxis)
            x
          -
         spatial3.d
            xAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q zAxis)
            x) := by
    funext x

    have hLap :=
      hPDE.curlLaplacianY_eq_laplacianVorticityY
        hs x

    have hLap' :
        spatial3.d
            zAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 ux)
            x
          -
        spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uz)
            x
          =
        PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (fun y : Point3 =>
            realVorticityY
              (logSpaceTimeVectorField u) s y)
          x := by
      simpa [ux, uz] using hLap

    have hAdv :=
      hPDE.curlAdvectionY_eq_transport_sub_stretch
        hs x

    unfold h3LoggedPreterminalVorticityRHSY
    linarith [hLap', hAdv]
  rw [hEq]
  exact
    (hLapXDeriv.sub hLapZDeriv).sub
      (hAdvXDeriv.sub hAdvZDeriv)

/-- The z-component pressure-free vorticity RHS is continuous in space at each
strict preterminal time. -/
theorem h3LoggedPreterminalVorticityRHSZ_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (h3LoggedPreterminalVorticityRHSZ u s) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let uy : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component yAxis

  let ux : ScalarField3 :=
    fun y : Point3 =>
      (logSpaceTimeVectorField u s y).component xAxis

  have huy3 : SpatialC3 uy := by
    simpa [uy] using
      hPDE.regularity.velocity_spatial_three
        s hs yAxis

  have hux3 : SpatialC3 ux := by
    simpa [ux] using
      hPDE.regularity.velocity_spatial_three
        s hs xAxis

  have hLapY :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uy) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huy3

  have hLapX :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 ux) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      hux3

  have hAdvY :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x yAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs yAxis

  have hAdvX :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            s x xAxis) :=
    hPDE.realAdvectionComponent_spatialC1
      hs xAxis

  have hLapYDeriv :
      Continuous
        (spatial3.d
          xAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 uy)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapY xAxis

  have hLapXDeriv :
      Continuous
        (spatial3.d
          yAxis
          (PrimeTensor.Bridge.RealFluid.laplacian
            spatial3 ux)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hLapX yAxis

  have hAdvYDeriv :
      Continuous
        (spatial3.d
          xAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x yAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvY xAxis

  have hAdvXDeriv :
      Continuous
        (spatial3.d
          yAxis
          (fun x : Point3 =>
            realAdvectionComponent
              (logSpaceTimeVectorField u)
              s x xAxis)) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hAdvX yAxis

  have hEq :
      h3LoggedPreterminalVorticityRHSZ u s
        =
      fun x : Point3 =>
        (spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uy)
            x
          -
         spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 ux)
            x)
          -
        (spatial3.d
            xAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q yAxis)
            x
          -
         spatial3.d
            yAxis
            (fun q : Point3 =>
              realAdvectionComponent
                (logSpaceTimeVectorField u)
                s q xAxis)
            x) := by
    funext x

    have hLap :=
      hPDE.curlLaplacianZ_eq_laplacianVorticityZ
        hs x

    have hLap' :
        spatial3.d
            xAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uy)
            x
          -
        spatial3.d
            yAxis
            (PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 ux)
            x
          =
        PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (fun y : Point3 =>
            realVorticityZ
              (logSpaceTimeVectorField u) s y)
          x := by
      simpa [uy, ux] using hLap

    have hAdv :=
      hPDE.curlAdvectionZ_eq_transport_sub_stretch
        hs x

    unfold h3LoggedPreterminalVorticityRHSZ
    linarith [hLap', hAdv]
  rw [hEq]
  exact
    (hLapYDeriv.sub hLapXDeriv).sub
      (hAdvYDeriv.sub hAdvXDeriv)

/-- At a fixed strict preterminal time, the actual x-vorticity temporal
derivative is continuous as a function of space. -/
theorem h3LoggedPreterminalVorticityX_temporalDerivative_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityX
              (logSpaceTimeVectorField u) r x)
          s) := by
  have hEq :
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityX
              (logSpaceTimeVectorField u) r x)
          s)
        =
      h3LoggedPreterminalVorticityRHSX u s := by
    funext x
    have h :=
      (h3LoggedPreterminalVorticityX_hasDerivAt
        hNS hs x).deriv
    simpa only [temporal_d] using h

  rw [hEq]
  exact
    h3LoggedPreterminalVorticityRHSX_continuous_space
      hNS hs

/-- At a fixed strict preterminal time, the actual y-vorticity temporal
derivative is continuous as a function of space. -/
theorem h3LoggedPreterminalVorticityY_temporalDerivative_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityY
              (logSpaceTimeVectorField u) r x)
          s) := by
  have hEq :
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityY
              (logSpaceTimeVectorField u) r x)
          s)
        =
      h3LoggedPreterminalVorticityRHSY u s := by
    funext x
    have h :=
      (h3LoggedPreterminalVorticityY_hasDerivAt
        hNS hs x).deriv
    simpa only [temporal_d] using h

  rw [hEq]
  exact
    h3LoggedPreterminalVorticityRHSY_continuous_space
      hNS hs

/-- At a fixed strict preterminal time, the actual z-vorticity temporal
derivative is continuous as a function of space. -/
theorem h3LoggedPreterminalVorticityZ_temporalDerivative_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    Continuous
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityZ
              (logSpaceTimeVectorField u) r x)
          s) := by
  have hEq :
      (fun x : Point3 =>
        temporal.d
          (fun r : ℝ =>
            realVorticityZ
              (logSpaceTimeVectorField u) r x)
          s)
        =
      h3LoggedPreterminalVorticityRHSZ u s := by
    funext x
    have h :=
      (h3LoggedPreterminalVorticityZ_hasDerivAt
        hNS hs x).deriv
    simpa only [temporal_d] using h

  rw [hEq]
  exact
    h3LoggedPreterminalVorticityRHSZ_continuous_space
      hNS hs

end

end Euclidean
end Bridge
end PrimeTensor
