import PrimeTensor.Bridge.Euclidean.Vorticity.Equation

/-!
# Native multiplicative vorticity balance: x-component

The classical three-dimensional vorticity equation is now fully formalized.
This file returns to the intrinsic multiplicative side.

For the x-component we define four native `MulReal` states:

* `mulTemporalVorticityX` — time response of native vorticity;
* `mulVorticityTransportX` — native representation of `(u · ∇)ωₓ`;
* `mulVortexStretchComponent ... xAxis` — already-existing native stretching;
* `mulVorticityDiffusionX` — native representation of `Δωₓ`.

Their logarithms are exactly the four corresponding classical real terms.
Consequently the additive classical balance

    ∂ₜωₓ + (u · ∇)ωₓ = (ω · ∇)uₓ + Δωₓ

is equivalent to the zero-free multiplicative balance

    Θₓ * Tₓ = Sₓ * Dₓ.

This is still an exact logarithmic conjugate of the classical equation.  The
point of exposing it is to create native states on which later scale-depth
statements can be made without immediately collapsing through `logEquiv`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Native temporal response of the x-vorticity state. -/
noncomputable def mulTemporalVorticityX
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
      mulVorticityX u τ x)
    t

/--
Native transport state for `(u · ∇)ωₓ`.

Each real scalar product is represented by the canonical log-product coupling;
the final three-term sum is represented by multiplication.
-/
noncomputable def mulVorticityTransportX
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
            mulVorticityX u t y)
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
              mulVorticityX u t y)
            x
        )
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ((u t x).component zAxis)
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityX u t y)
            x
        )
  )

/--
Native diffusion state for `Δωₓ`.

Each same-axis second derivative is already a native differential response.
The classical sum of the three second derivatives is represented by
multiplication.
-/
noncomputable def mulVorticityDiffusionX
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
            mulVorticityX u t y)
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
              mulVorticityX u t y)
        )
        x
      *
    mulSpatial3.d
        zAxis
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              mulVorticityX u t y)
        )
        x
  )

/-- The logarithm of native temporal x-vorticity is `∂ₜωₓ`. -/
theorem logValue_mulTemporalVorticityX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulTemporalVorticityX u t x)
      =
    temporal.d
      (
        fun τ =>
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      )
      t := by

  unfold mulTemporalVorticityX

  have hTime :=
    PrimeTensor.Bridge.Euclidean.mulTemporal_compatible.d_log
      (fun τ =>
        mulVorticityX u τ x)
      t

  rw [← hTime]

  have hω :
      (
        fun τ =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityX u τ x)
      )
        =
      (
        fun τ =>
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            τ x
      ) := by

    funext τ
    exact logValue_mulVorticityX u τ x

  rw [hω]

/-- The logarithm of native x-vorticity transport is `(u · ∇)ωₓ`. -/
theorem logValue_mulVorticityTransportX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityTransportX u t x)
      =
    realVorticityTransportX
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityTransportX
  unfold realVorticityTransportX

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
            (mulVorticityX u t y)
      )
        =
      (
        fun y =>
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityX u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        mulVorticityX u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        mulVorticityX u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        mulVorticityX u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]

  unfold
    PrimeTensor.Bridge.logSpaceTimeVectorField
    PrimeTensor.Bridge.logVectorField

  rfl

/-- The logarithm of native x-vorticity diffusion is `Δωₓ`. -/
theorem logValue_mulVorticityDiffusionX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityDiffusionX u t x)
      =
    PrimeTensor.Bridge.RealFluid.laplacian
      spatial3
      (
        fun y =>
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      )
      x := by

  unfold mulVorticityDiffusionX

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul
  ]

  have hω :
      (
        fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityX u t y)
      )
        =
      (
        fun y =>
          realVorticityX
            (PrimeTensor.Bridge.logSpaceTimeVectorField u)
            t y
      ) := by

    funext y
    exact logValue_mulVorticityX u t y

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      xAxis
      (fun y =>
        mulVorticityX u t y)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      yAxis
      (fun y =>
        mulVorticityX u t y)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d2_log
      zAxis
      (fun y =>
        mulVorticityX u t y)
      x

  rw [← hx, ← hy, ← hz]
  rw [hω]
  rw [laplacian3_eq]

/--
The intrinsic x-vorticity balance:

    Θₓ * Tₓ = Sₓ * Dₓ.
-/
def MulVorticityBalanceX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) : Prop :=

  mulTemporalVorticityX u t x
      *
    mulVorticityTransportX u t x
    =
  mulVortexStretchComponent
      u t x xAxis
      *
    mulVorticityDiffusionX u t x

/--
The native multiplicative x-vorticity balance is exactly equivalent, under
`logValue`, to the classical additive x-vorticity equation for the logged
velocity field.
-/
theorem mulVorticityBalanceX_iff_loggedEquation
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulVorticityBalanceX u t x
      ↔
    temporal.d
        (
          fun τ =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              τ x
        )
        t
      +
    realVorticityTransportX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
      =
    realVortexStretchComponent
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x xAxis
      +
    PrimeTensor.Bridge.RealFluid.laplacian
        spatial3
        (
          fun y =>
            realVorticityX
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

    unfold MulVorticityBalanceX at h

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityX,
      logValue_mulVorticityTransportX,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionX
    ] at hLog

    exact hLog

  · intro h

    unfold MulVorticityBalanceX

    apply PrimeTensor.Bridge.MulReal.logValue_injective

    rw [
      PrimeTensor.Bridge.MulReal.logValue_mul,
      PrimeTensor.Bridge.MulReal.logValue_mul,
      logValue_mulTemporalVorticityX,
      logValue_mulVorticityTransportX,
      logValue_mulVortexStretchComponent,
      logValue_mulVorticityDiffusionX
    ]

    exact h

end Euclidean
end Bridge
end PrimeTensor
