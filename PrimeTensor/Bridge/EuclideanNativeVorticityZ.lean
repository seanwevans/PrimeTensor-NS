import PrimeTensor.Bridge.EuclideanNativeVorticityY

/-!
# Native multiplicative vorticity balance: z-component

The x- and y-components have already been returned to the intrinsic
multiplicative language.  This file performs the cyclic z-component
construction.

The classical balance

    ∂ₜω_z + (u · ∇)ω_z = (ω · ∇)u_z + Δω_z

is represented intrinsically as

    Θ_z * T_z = S_z * D_z.

As in the previous component files, the logarithmic bridge is used only to
prove semantic equivalence.  The balance itself is a proposition entirely on
`MulReal`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Native temporal response of the z-vorticity state. -/
noncomputable def mulTemporalVorticityZ
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
      mulVorticityZ u τ x)
    t

/--
Native transport state for `(u · ∇)ω_z`.
-/
noncomputable def mulVorticityTransportZ
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
            mulVorticityZ u t y)
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
              mulVorticityZ u t y)
            x
        )
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ((u t x).component zAxis)
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityZ u t y)
            x
        )
  )

/--
Native diffusion state for `Δω_z`.
-/
noncomputable def mulVorticityDiffusionZ
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
            mulVorticityZ u t y)
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
              mulVorticityZ u t y)
        )
        x
      *
    mulSpatial3.d
        zAxis
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityZ u t y)
        )
        x
  )

/-- The logarithm of native temporal z-vorticity is `∂ₜω_z`. -/
theorem logValue_mulTemporalVorticityZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulTemporalVorticityZ u t x)
      =
    temporal.d
      (
        fun τ =>
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      )
      t := by

  unfold mulTemporalVorticityZ

  have hTime :=
    PrimeTensor.Bridge.Euclidean.mulTemporal_compatible.d_log
      (fun τ =>
        mulVorticityZ u τ x)
      t

  rw [← hTime]

  have hω :
      (
        fun τ =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityZ u τ x)
      )
        =
      (
        fun τ =>
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      ) := by

    funext τ
    exact logValue_mulVorticityZ u τ x

  rw [hω]

/-- The logarithm of native z-vorticity transport is `(u · ∇)ω_z`. -/
theorem logValue_mulVorticityTransportZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityTransportZ u t x)
      =
    realVorticityTransportZ
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityTransportZ
  unfold realVorticityTransportZ

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
            (mulVorticityZ u t y)
      )
        =
      (
        fun y =>
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityZ u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]

  unfold
    PrimeTensor.Bridge.logSpaceTimeVectorField
    PrimeTensor.Bridge.logVectorField

  rfl

/-- The logarithm of native z-vorticity diffusion is `Δω_z`. -/
theorem logValue_mulVorticityDiffusionZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityDiffusionZ u t x)
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      )
      x := by

  unfold mulVorticityDiffusionZ

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul
  ]

  have hω :
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityZ u t y)
      )
        =
      (
        fun y =>
          realVorticityZ
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityZ u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      xAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      yAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      zAxis
      (fun y =>
        mulVorticityZ u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]
  rw [laplacian3_eq]

/--
The intrinsic z-vorticity balance:

    Θ_z * T_z = S_z * D_z.
-/
def MulVorticityBalanceZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) : Prop :=

  mulTemporalVorticityZ u t x
      *
    mulVorticityTransportZ u t x
    =
  mulVortexStretchComponent
      u t x zAxis
      *
    mulVorticityDiffusionZ u t x

/--
The native multiplicative z-vorticity balance is exactly equivalent, under
`logValue`, to the classical additive z-vorticity equation for the logged
velocity field.
-/
theorem mulVorticityBalanceZ_iff_loggedEquation
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulVorticityBalanceZ u t x
      ↔
    temporal.d
        (
          fun τ =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      +
    realVorticityTransportZ
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
      =
    realVortexStretchComponent
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x zAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (
          fun y =>
            realVorticityZ
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

    unfold MulVorticityBalanceZ at h

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityZ,
      logValue_mulVorticityTransportZ,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionZ
    ] at hLog

    exact hLog

  · intro h

    unfold MulVorticityBalanceZ

    apply PrimeTensor.Bridge.MulReal.logValue_injective

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityZ,
      logValue_mulVorticityTransportZ,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionZ
    ]

    exact h

end Euclidean
end Bridge
end PrimeTensor
