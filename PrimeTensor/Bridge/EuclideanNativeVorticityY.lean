import PrimeTensor.Bridge.EuclideanNativeVorticityX

/-!
# Native multiplicative vorticity balance: y-component

The x-component has already been returned to the intrinsic multiplicative
language.  This file performs the cyclic y-component construction.

The classical balance

    ∂ₜω_y + (u · ∇)ω_y = (ω · ∇)u_y + Δω_y

is represented intrinsically as

    Θ_y * T_y = S_y * D_y.

As in the x-component file, the logarithmic bridge is used only to prove
semantic equivalence.  The balance itself is a proposition entirely on
`MulReal`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Native temporal response of the y-vorticity state. -/
noncomputable def mulTemporalVorticityY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=
  mulTemporal.d
    (fun τ =>
      mulVorticityY u τ x)
    t

/--
Native transport state for `(u · ∇)ω_y`.
-/
noncomputable def mulVorticityTransportY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=

  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
      ((u t x).component xAxis)
      (
        mulSpatial3.d
          xAxis
          (fun y =>
            mulVorticityY u t y)
          x
      )
    *
  (
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ((u t x).component yAxis)
        (
          mulSpatial3.d
            yAxis
            (fun y =>
              mulVorticityY u t y)
            x
        )
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ((u t x).component zAxis)
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityY u t y)
            x
        )
  )

/--
Native diffusion state for `Δω_y`.
-/
noncomputable def mulVorticityDiffusionY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=

  mulSpatial3.d
      xAxis
      (
        mulSpatial3.d
          xAxis
          (fun y =>
            mulVorticityY u t y)
      )
      x
    *
  (
    mulSpatial3.d
        yAxis
        (
          mulSpatial3.d
            yAxis
            (fun y =>
              mulVorticityY u t y)
        )
        x
      *
    mulSpatial3.d
        zAxis
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityY u t y)
        )
        x
  )

/-- The logarithm of native temporal y-vorticity is `∂ₜω_y`. -/
theorem logValue_mulTemporalVorticityY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulTemporalVorticityY u t x)
      =
    temporal.d
      (
        fun τ =>
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      )
      t := by

  unfold mulTemporalVorticityY

  have hTime :=
    PrimeTensor.Bridge.Euclidean.mulTemporal_compatible.d_log
      (fun τ =>
        mulVorticityY u τ x)
      t

  rw [← hTime]

  have hω :
      (
        fun τ =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityY u τ x)
      )
        =
      (
        fun τ =>
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      ) := by

    funext τ
    exact logValue_mulVorticityY u τ x

  rw [hω]

/-- The logarithm of native y-vorticity transport is `(u · ∇)ω_y`. -/
theorem logValue_mulVorticityTransportY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityTransportY u t x)
      =
    realVorticityTransportY
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityTransportY
  unfold realVorticityTransportY

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue
  ]

  have hω :
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityY u t y)
      )
        =
      (
        fun y =>
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityY u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        mulVorticityY u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        mulVorticityY u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        mulVorticityY u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]

  unfold
    PrimeTensor.Bridge.logSpaceTimeVectorField
    PrimeTensor.Bridge.logVectorField

  rfl

/-- The logarithm of native y-vorticity diffusion is `Δω_y`. -/
theorem logValue_mulVorticityDiffusionY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityDiffusionY u t x)
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      )
      x := by

  unfold mulVorticityDiffusionY

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul
  ]

  have hω :
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityY u t y)
      )
        =
      (
        fun y =>
          realVorticityY
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityY u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      xAxis
      (fun y =>
        mulVorticityY u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      yAxis
      (fun y =>
        mulVorticityY u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      zAxis
      (fun y =>
        mulVorticityY u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]
  rw [laplacian3_eq]

/--
The intrinsic y-vorticity balance:

    Θ_y * T_y = S_y * D_y.
-/
def MulVorticityBalanceY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) : Prop :=

  mulTemporalVorticityY u t x
      *
    mulVorticityTransportY u t x
    =
  mulVortexStretchComponent
      u t x yAxis
      *
    mulVorticityDiffusionY u t x

/--
The native multiplicative y-vorticity balance is exactly equivalent, under
`logValue`, to the classical additive y-vorticity equation for the logged
velocity field.
-/
theorem mulVorticityBalanceY_iff_loggedEquation
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulVorticityBalanceY u t x
      ↔
    temporal.d
        (
          fun τ =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      +
    realVorticityTransportY
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
      =
    realVortexStretchComponent
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x yAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (
          fun y =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t y
        )
        x := by

  constructor

  · intro h

    have hLog :=
      congrArg
        PrimeTensor.Bridge.MulReal.logValue
        h

    unfold MulVorticityBalanceY at h

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityY,
      logValue_mulVorticityTransportY,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionY
    ] at hLog

    exact hLog

  · intro h

    unfold MulVorticityBalanceY

    apply PrimeTensor.Bridge.MulReal.logValue_injective

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityY,
      logValue_mulVorticityTransportY,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionY
    ]

    exact h

end Euclidean
end Bridge
end PrimeTensor