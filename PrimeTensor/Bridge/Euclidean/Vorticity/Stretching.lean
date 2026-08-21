import PrimeTensor.Bridge.Euclidean.Vorticity

/-!
# Multiplicative vortex stretching in three dimensions

The dangerous specifically-three-dimensional term in the vorticity equation is

    (ω · ∇)v.

Before deriving the full vorticity PDE, we isolate this term algebraically.
Doing so avoids introducing mixed-partial commutation before it is actually
needed.

For each output component `j`, the ordinary stretching term is

    ωₓ ∂x v_j + ωᵧ ∂y v_j + ω_z ∂z v_j.

The multiplicative representation uses the canonical log-product coupling for
each scalar product and ordinary multiplication for the final sum:

    C(Ωₓ, DₓU_j)
      * C(Ωᵧ, DᵧU_j)
      * C(Ω_z, D_zU_j).

Its logarithm is exactly the classical stretching component.

We then contract once more with vorticity itself.  This gives a native scalar
whose logarithm is

    ω · ((ω · ∇)v),

the vortex-stretching contribution to pointwise enstrophy production.

No estimate is claimed here.  The purpose is to expose the exact intrinsic
object whose scale growth would have to be controlled to obstruct blow-up.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Classical `j`-component of vortex stretching `(ω · ∇)v`.
-/
noncomputable def realVortexStretchComponent
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : ℝ :=

  realVorticityX v t x *
      spatial3.d
        xAxis
        (fun y =>
          (v t y).component j)
        x
    +
  (
    realVorticityY v t x *
        spatial3.d
          yAxis
          (fun y =>
            (v t y).component j)
          x
      +
    realVorticityZ v t x *
        spatial3.d
          zAxis
          (fun y =>
            (v t y).component j)
          x
  )

/--
Native subtraction-free `j`-component of vortex stretching.

Each classical scalar multiplication is represented by the canonical
log-product coupling; the classical sum is represented by multiplication.
-/
noncomputable def mulVortexStretchComponent
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.MulReal :=

  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
      (mulVorticityX u t x)
      (
        mulSpatial3.d
          xAxis
          (fun y =>
            (u t y).component j)
          x
      )
    *
  (
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        (mulVorticityY u t x)
        (
          mulSpatial3.d
            yAxis
            (fun y =>
              (u t y).component j)
            x
        )
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        (mulVorticityZ u t x)
        (
          mulSpatial3.d
            zAxis
            (fun y =>
              (u t y).component j)
            x
        )
  )

/--
The logarithm of the native stretching component is exactly the classical
vortex-stretching component of the logged velocity.
-/
theorem logValue_mulVortexStretchComponent
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVortexStretchComponent u t x j)
      =
    realVortexStretchComponent
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x j := by

  unfold mulVortexStretchComponent

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    logValue_mulVorticityX,
    logValue_mulVorticityY,
    logValue_mulVorticityZ
  ]

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        (u t y).component j)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        (u t y).component j)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        (u t y).component j)
      x

  rw [← hx, ← hy, ← hz]

  rfl

/--
Classical pointwise vortex-stretching contribution to enstrophy production:

    ω · ((ω · ∇)v).
-/
noncomputable def realEnstrophyStretchProduction
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=

  realVorticityX v t x *
      realVortexStretchComponent
        v t x xAxis
    +
  (
    realVorticityY v t x *
        realVortexStretchComponent
          v t x yAxis
      +
    realVorticityZ v t x *
        realVortexStretchComponent
          v t x zAxis
  )

/--
Native scalar vortex-stretching production state.

Its logarithm is the classical scalar

    ω · ((ω · ∇)v).
-/
noncomputable def mulEnstrophyStretchProduction
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=

  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
      (mulVorticityX u t x)
      (mulVortexStretchComponent u t x xAxis)
    *
  (
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        (mulVorticityY u t x)
        (mulVortexStretchComponent u t x yAxis)
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        (mulVorticityZ u t x)
        (mulVortexStretchComponent u t x zAxis)
  )

/--
The logarithm of the native scalar stretching-production state is exactly the
classical pointwise vortex-stretching contribution to enstrophy production.
-/
theorem logValue_mulEnstrophyStretchProduction
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulEnstrophyStretchProduction u t x)
      =
    realEnstrophyStretchProduction
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulEnstrophyStretchProduction

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue,
    logValue_mulVorticityX,
    logValue_mulVorticityY,
    logValue_mulVorticityZ,
    logValue_mulVortexStretchComponent,
    logValue_mulVortexStretchComponent,
    logValue_mulVortexStretchComponent
  ]

  rfl

/--
A native vorticity component is at the multiplicative pivot exactly when the
corresponding classical vorticity component is zero.
-/
theorem mulVorticityX_eq_one_iff
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    mulVorticityX u t x = 1
      ↔
    realVorticityX
        (PrimeTensor.Bridge.logSpaceTimeVectorField u)
        t x
      =
    0 := by

  constructor

  · intro h

    have hLog :=
      congrArg
        PrimeTensor.Bridge.MulReal.logValue
        h

    rw [
      logValue_mulVorticityX,
      PrimeTensor.Bridge.MulReal.logValue_one
    ] at hLog

    exact hLog

  · intro h

    apply
      PrimeTensor.Bridge.MulReal.logValue_injective

    rw [
      logValue_mulVorticityX,
      PrimeTensor.Bridge.MulReal.logValue_one,
      h
    ]

/--
The native enstrophy state is at the multiplicative pivot exactly when all
three classical vorticity components vanish.
-/
theorem mulEnstrophyDensity_eq_one_iff
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    mulEnstrophyDensity u t x = 1
      ↔
    (
      realVorticityX
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
        =
      0
      ∧
      realVorticityY
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
        =
      0
      ∧
      realVorticityZ
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
        =
      0
    ) := by

  constructor

  · intro h

    have hLog :=
      congrArg
        PrimeTensor.Bridge.MulReal.logValue
        h

    rw [
      logValue_mulEnstrophyDensity,
      PrimeTensor.Bridge.MulReal.logValue_one
    ] at hLog

    unfold realEnstrophyDensity at hLog

    constructor

    · nlinarith [
        sq_nonneg
          (
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          ),
        sq_nonneg
          (
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
          )
      ]

    · constructor

      · nlinarith [
          sq_nonneg
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            ),
          sq_nonneg
            (
              realVorticityZ
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            )
        ]

      · nlinarith [
          sq_nonneg
            (
              realVorticityX
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            ),
          sq_nonneg
            (
              realVorticityY
                (PrimeTensor.Bridge.logSpaceTimeVectorField u)
                t x
            )
        ]

  · rintro ⟨hx, hy, hz⟩

    apply
      PrimeTensor.Bridge.MulReal.logValue_injective

    rw [
      logValue_mulEnstrophyDensity,
      PrimeTensor.Bridge.MulReal.logValue_one
    ]

    unfold realEnstrophyDensity

    rw [hx, hy, hz]

    ring

end Euclidean
end Bridge
end PrimeTensor
