import PrimeTensor.Bridge.Euclidean.Vorticity.Regularity

/-!
# Linear curl identities for vorticity-regular solutions

This file proves the two linear identities needed before curling the nonlinear
Navier--Stokes momentum equation:

1. time differentiation commutes with each vorticity component;
2. the curl of the pressure gradient vanishes.

The first uses the genuine mixed spacetime `HasDerivAt` witnesses introduced in
`EuclideanVorticityRegularity`, so no argument depends on fallback values of
Mathlib's total `deriv`.

The second is exactly Schwarz symmetry for the spatially `C²` pressure.

The remaining linear identity, `curl (Δu) = Δ(curl u)`, is intentionally left
for the next module because it is the first place where the additional
`C³_x` velocity hypothesis is genuinely consumed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

namespace VorticitySolution3

/--
Time differentiation commutes with the `x`-vorticity component.
-/
theorem temporal_realVorticityX
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityX
            s.velocity
            τ x)
        t
      =
    spatial3.d
        yAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component zAxis
              )
              t
        )
        x
      -
    spatial3.d
        zAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component yAxis
              )
              t
        )
        x := by

  have hy :=
    s.velocity_space_time_hasDerivAt
      t x yAxis zAxis

  have hz :=
    s.velocity_space_time_hasDerivAt
      t x zAxis yAxis

  have hsub :=
    hy.sub hz

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                yAxis
                (
                  fun y =>
                    (s.velocity τ y).component zAxis
                )
                x
              -
            spatial3.d
                zAxis
                (
                  fun y =>
                    (s.velocity τ y).component yAxis
                )
                x
        )
        t
      =
    spatial3.d
        yAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component zAxis
              )
              t
        )
        x
      -
    spatial3.d
        zAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component yAxis
              )
              t
        )
        x

  exact
    hsub.deriv

/--
Time differentiation commutes with the `y`-vorticity component.
-/
theorem temporal_realVorticityY
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityY
            s.velocity
            τ x)
        t
      =
    spatial3.d
        zAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component xAxis
              )
              t
        )
        x
      -
    spatial3.d
        xAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component zAxis
              )
              t
        )
        x := by

  have hz :=
    s.velocity_space_time_hasDerivAt
      t x zAxis xAxis

  have hx :=
    s.velocity_space_time_hasDerivAt
      t x xAxis zAxis

  have hsub :=
    hz.sub hx

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                zAxis
                (
                  fun y =>
                    (s.velocity τ y).component xAxis
                )
                x
              -
            spatial3.d
                xAxis
                (
                  fun y =>
                    (s.velocity τ y).component zAxis
                )
                x
        )
        t
      =
    spatial3.d
        zAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component xAxis
              )
              t
        )
        x
      -
    spatial3.d
        xAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component zAxis
              )
              t
        )
        x

  exact
    hsub.deriv

/--
Time differentiation commutes with the `z`-vorticity component.
-/
theorem temporal_realVorticityZ
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    temporal.d
        (fun τ =>
          realVorticityZ
            s.velocity
            τ x)
        t
      =
    spatial3.d
        xAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component yAxis
              )
              t
        )
        x
      -
    spatial3.d
        yAxis
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component xAxis
              )
              t
        )
        x := by

  have hx :=
    s.velocity_space_time_hasDerivAt
      t x xAxis yAxis

  have hy :=
    s.velocity_space_time_hasDerivAt
      t x yAxis xAxis

  have hsub :=
    hx.sub hy

  unfold temporal

  change
    deriv
        (
          fun τ =>
            spatial3.d
                xAxis
                (
                  fun y =>
                    (s.velocity τ y).component yAxis
                )
                x
              -
            spatial3.d
                yAxis
                (
                  fun y =>
                    (s.velocity τ y).component xAxis
                )
                x
        )
        t
      =
    spatial3.d
        xAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component yAxis
              )
              t
        )
        x
      -
    spatial3.d
        yAxis
        (
          fun y =>
            deriv
              (
                fun τ =>
                  (s.velocity τ y).component xAxis
              )
              t
        )
        x

  exact
    hsub.deriv

/--
The `x`-component of `curl (grad p)` vanishes.
-/
theorem pressureCurlX_eq_zero
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        yAxis
        (
          spatial3.d
            zAxis
            (s.pressure t)
        )
        x
      -
    spatial3.d
        zAxis
        (
          spatial3.d
            yAxis
            (s.pressure t)
        )
        x
      =
    0 := by

  have h :=
    s.pressure_spatial_d_comm
      t x yAxis zAxis

  rw [h]

  ring

/--
The `y`-component of `curl (grad p)` vanishes.
-/
theorem pressureCurlY_eq_zero
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        zAxis
        (
          spatial3.d
            xAxis
            (s.pressure t)
        )
        x
      -
    spatial3.d
        xAxis
        (
          spatial3.d
            zAxis
            (s.pressure t)
        )
        x
      =
    0 := by

  have h :=
    s.pressure_spatial_d_comm
      t x zAxis xAxis

  rw [h]

  ring

/--
The `z`-component of `curl (grad p)` vanishes.
-/
theorem pressureCurlZ_eq_zero
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
        xAxis
        (
          spatial3.d
            yAxis
            (s.pressure t)
        )
        x
      -
    spatial3.d
        yAxis
        (
          spatial3.d
            xAxis
            (s.pressure t)
        )
        x
      =
    0 := by

  have h :=
    s.pressure_spatial_d_comm
      t x xAxis yAxis

  rw [h]

  ring

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
