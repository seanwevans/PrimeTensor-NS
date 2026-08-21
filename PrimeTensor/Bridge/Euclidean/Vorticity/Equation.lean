import PrimeTensor.Bridge.Euclidean.Vorticity.Equation.X

/-!
# Classical vorticity equation: remaining components

The x-component is already proved in `EuclideanVorticityEquationX`.
This file adds the cyclic y- and z-components:

    ∂ₜω_y + (u · ∇)ω_y = (ω · ∇)u_y + Δω_y

and

    ∂ₜω_z + (u · ∇)ω_z = (ω · ∇)u_z + Δω_z.

No new analysis is needed: each proof assembles previously established
time-curl, nonlinear curl, pressure-curl, and Laplacian-curl identities.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

namespace VorticitySolution3

/--
The y-component of the normalized three-dimensional incompressible
vorticity equation.
-/
theorem vorticityEquationY
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityY
            s.velocity τ x)
        t
      +
    realVorticityTransportY
        s.velocity t x
      =
    realVortexStretchComponent
        s.velocity t x yAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityY
            s.velocity t y)
        x := by

  rw [
    s.temporal_realVorticityY
      t x,
    s.spatial_d_temporalComponent
      t x zAxis xAxis,
    s.spatial_d_temporalComponent
      t x xAxis zAxis
  ]

  have hAdv :=
    s.curlAdvectionY_eq_transport_sub_stretch
      t x

  have hPressure :=
    s.pressureCurlY_eq_zero
      t x

  have hLaplacian :=
    s.curlLaplacianY_eq_laplacianVorticityY
      t x

  linarith

/--
The z-component of the normalized three-dimensional incompressible
vorticity equation.
-/
theorem vorticityEquationZ
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityZ
            s.velocity τ x)
        t
      +
    realVorticityTransportZ
        s.velocity t x
      =
    realVortexStretchComponent
        s.velocity t x zAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (fun y =>
          realVorticityZ
            s.velocity t y)
        x := by

  rw [
    s.temporal_realVorticityZ
      t x,
    s.spatial_d_temporalComponent
      t x xAxis yAxis,
    s.spatial_d_temporalComponent
      t x yAxis xAxis
  ]

  have hAdv :=
    s.curlAdvectionZ_eq_transport_sub_stretch
      t x

  have hPressure :=
    s.pressureCurlZ_eq_zero
      t x

  have hLaplacian :=
    s.curlLaplacianZ_eq_laplacianVorticityZ
      t x

  linarith

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
