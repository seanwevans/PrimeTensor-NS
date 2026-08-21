import PrimeTensor.Bridge.EuclideanNavierStokes

/-!
# Multiplicative vorticity and enstrophy in three dimensions

The explicit Euclidean Navier--Stokes bridge lets us ask which classical
structures become simpler in the zero-free multiplicative language.

Curl is the first important example.

For a multiplicative velocity `U` with logarithmic velocity `v = L ∘ U`,
classical vorticity contains differences of cross-derivatives:

    ωₓ = ∂y v_z - ∂z v_y
    ωᵧ = ∂z v_x - ∂x v_z
    ω_z = ∂x v_y - ∂y v_x.

Because logarithms turn multiplicative ratios into differences, each component
has a native subtraction-free representative:

    Ωₓ = (D_y U_z) / (D_z U_y)
    Ωᵧ = (D_z U_x) / (D_x U_z)
    Ω_z = (D_x U_y) / (D_y U_x).

The first three main theorems prove exactly

    L(Ωᵢ) = ωᵢ.

The canonical log-product coupling then gives a zero-free representative of
pointwise enstrophy density.  Since

    L(C(a,a)) = L(a)^2,

the product

    E = C(Ωₓ,Ωₓ) * C(Ωᵧ,Ωᵧ) * C(Ω_z,Ω_z)

satisfies

    L(E) = ωₓ² + ωᵧ² + ω_z².

This is not yet an enstrophy estimate or a regularity theorem.  It is the
intrinsic object on which such an estimate can be sought.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Classical `x`-component of vorticity for a real three-dimensional spacetime
velocity field.
-/
noncomputable def realVorticityX
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  spatial3.d
      yAxis
      (fun y =>
        (v t y).component zAxis)
      x
    -
  spatial3.d
      zAxis
      (fun y =>
        (v t y).component yAxis)
      x

/--
Classical `y`-component of vorticity.
-/
noncomputable def realVorticityY
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  spatial3.d
      zAxis
      (fun y =>
        (v t y).component xAxis)
      x
    -
  spatial3.d
      xAxis
      (fun y =>
        (v t y).component zAxis)
      x

/--
Classical `z`-component of vorticity.
-/
noncomputable def realVorticityZ
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  spatial3.d
      xAxis
      (fun y =>
        (v t y).component yAxis)
      x
    -
  spatial3.d
      yAxis
      (fun y =>
        (v t y).component xAxis)
      x

/--
Native subtraction-free `x`-vorticity component.

The classical difference is represented by an oriented multiplicative ratio.
-/
noncomputable def mulVorticityX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=
  PrimeTensor.MulReal.ratio
    (
      mulSpatial3.d
        yAxis
        (fun y =>
          (u t y).component zAxis)
        x
    )
    (
      mulSpatial3.d
        zAxis
        (fun y =>
          (u t y).component yAxis)
        x
    )

/--
Native subtraction-free `y`-vorticity component.
-/
noncomputable def mulVorticityY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=
  PrimeTensor.MulReal.ratio
    (
      mulSpatial3.d
        zAxis
        (fun y =>
          (u t y).component xAxis)
        x
    )
    (
      mulSpatial3.d
        xAxis
        (fun y =>
          (u t y).component zAxis)
        x
    )

/--
Native subtraction-free `z`-vorticity component.
-/
noncomputable def mulVorticityZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=
  PrimeTensor.MulReal.ratio
    (
      mulSpatial3.d
        xAxis
        (fun y =>
          (u t y).component yAxis)
        x
    )
    (
      mulSpatial3.d
        yAxis
        (fun y =>
          (u t y).component xAxis)
        x
    )

/--
The native `x`-vorticity ratio logarithm is exactly the classical curl
component of the logged velocity.
-/
theorem logValue_mulVorticityX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityX u t x)
      =
    realVorticityX
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityX

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ratio
  ]

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        (u t y).component zAxis)
      x

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        (u t y).component yAxis)
      x

  rw [← hy, ← hz]

  rfl

/--
The native `y`-vorticity ratio logarithm is exactly the classical curl
component of the logged velocity.
-/
theorem logValue_mulVorticityY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityY u t x)
      =
    realVorticityY
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityY

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ratio
  ]

  have hz :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      zAxis
      (fun y =>
        (u t y).component xAxis)
      x

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        (u t y).component zAxis)
      x

  rw [← hz, ← hx]

  rfl

/--
The native `z`-vorticity ratio logarithm is exactly the classical curl
component of the logged velocity.
-/
theorem logValue_mulVorticityZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulVorticityZ u t x)
      =
    realVorticityZ
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulVorticityZ

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ratio
  ]

  have hx :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      xAxis
      (fun y =>
        (u t y).component yAxis)
      x

  have hy :=
    PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
      yAxis
      (fun y =>
        (u t y).component xAxis)
      x

  rw [← hx, ← hy]

  rfl

/--
Pointwise classical enstrophy density `|ω|²`.
-/
noncomputable def realEnstrophyDensity
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (t : ℝ)
    (x : Point3) : ℝ :=
  realVorticityX v t x *
      realVorticityX v t x
    +
  (
    realVorticityY v t x *
        realVorticityY v t x
      +
    realVorticityZ v t x *
        realVorticityZ v t x
  )

/--
Zero-free multiplicative representative of pointwise enstrophy density.

Each squared real vorticity component is represented by self-coupling under
the canonical completed log-product coupling, and the sum of the three squares
is represented by multiplication of those coupling states.
-/
noncomputable def mulEnstrophyDensity
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.MulReal :=

  let ωx :=
    mulVorticityX u t x

  let ωy :=
    mulVorticityY u t x

  let ωz :=
    mulVorticityZ u t x

  PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
      ωx ωx
    *
  (
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ωy ωy
      *
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
        ωz ωz
  )

/--
The logarithm of the native enstrophy state is exactly the classical
pointwise enstrophy density of the logged velocity.
-/
theorem logValue_mulEnstrophyDensity
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    PrimeTensor.Bridge.MulReal.logValue
        (mulEnstrophyDensity u t x)
      =
    realEnstrophyDensity
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      t x := by

  unfold mulEnstrophyDensity

  dsimp only

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

  rfl

/--
The logged native enstrophy state is nonnegative.
-/
theorem logValue_mulEnstrophyDensity_nonneg
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    0
      ≤
    PrimeTensor.Bridge.MulReal.logValue
      (mulEnstrophyDensity u t x) := by

  rw [
    logValue_mulEnstrophyDensity
  ]

  unfold realEnstrophyDensity

  nlinarith [
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
      ),
    sq_nonneg
      (
        realVorticityZ
          (PrimeTensor.Bridge.logSpaceTimeVectorField u)
          t x
      )
  ]

end Euclidean
end Bridge
end PrimeTensor
