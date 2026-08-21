import PrimeTensor.Bridge.Euclidean.Vorticity.Native.Z

/-!
# Native multiplicative vorticity balance in three dimensions

The three componentwise native balances are now available:

    Θ_x * T_x = S_x * D_x
    Θ_y * T_y = S_y * D_y
    Θ_z * T_z = S_z * D_z

This file packages them into a single three-dimensional proposition.  No new
analytic content is introduced here: the purpose is to give the native
vorticity equation a single object that later scale/refinement arguments can
consume without returning to the classical bridge component by component.

The proposition `MulVorticityBalance3` is entirely multiplicative.  The
companion theorem `mulVorticityBalance3_iff_loggedEquations` records its exact
semantic equivalence to the three classical logged vorticity equations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The full intrinsic three-dimensional vorticity balance.

Each component is expressed natively on `MulReal` as

    temporal * transport = stretching * diffusion.
-/
def MulVorticityBalance3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) : Prop :=
  MulVorticityBalanceX u t x ∧
  MulVorticityBalanceY u t x ∧
  MulVorticityBalanceZ u t x

/--
The full native multiplicative vorticity balance is exactly equivalent to the
three classical vorticity equations of the logged field.
-/
theorem mulVorticityBalance3_iff_loggedEquations
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulVorticityBalance3 u t x
      ↔
    (
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
          x
    )
    ∧
    (
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
          x
    )
    ∧
    (
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
          x
    ) := by

  unfold MulVorticityBalance3

  rw [
    mulVorticityBalanceX_iff_loggedEquation,
    mulVorticityBalanceY_iff_loggedEquation,
    mulVorticityBalanceZ_iff_loggedEquation
  ]

end Euclidean
end Bridge
end PrimeTensor
