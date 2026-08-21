import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeGradientBound

/-!
# Third-order H³ transport: full gradient-block pointwise bound

The axis-local `D³u · Du` estimate is already available.  This file combines
the three velocity-axis contributions into a single pointwise bound for the
full twelve-term gradient block.

No interpolation estimate and no spatial integration is used here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Three pointwise estimates combine through the triangle inequality.
-/
private theorem three_gradient_blocks_algebra_bound
    {
      H f gx gy gz mx my mz : ℝ
    }
    (hx : 2 * |f * gx| ≤ H * mx)
    (hy : 2 * |f * gy| ≤ H * my)
    (hz : 2 * |f * gz| ≤ H * mz) :
    2 * |f * (gx + (gy + gz))|
      ≤
    H * (mx + (my + mz)) := by

  have hRewrite :
      f * (gx + (gy + gz))
        =
      f * gx + (f * gy + f * gz) := by
    ring

  have hAbs :
      abs (f * (gx + (gy + gz)))
        ≤
      |f * gx| + (|f * gy| + |f * gz|) := by

    rw [hRewrite]

    exact
      le_trans
        (abs_add_le _ _)
        (
          add_le_add_right
            (abs_add_le _ _)
            _
        )

  have hAbsTwo :
      2 * abs (f * (gx + (gy + gz)))
        ≤
      2 * (|f * gx| + (|f * gy| + |f * gz|)) := by

    exact
      mul_le_mul_of_nonneg_left
        hAbs
        (by norm_num)

  nlinarith

/--
The square-density majorant for all twelve `D³u · Du` terms of the third-order
commutator.
-/
noncomputable def thirdOrderGradientMajorantDensity
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  thirdOrderAxisGradientMajorantDensity
      u t i k l j xAxis x
    +
  (
    thirdOrderAxisGradientMajorantDensity
        u t i k l j yAxis x
      +
    thirdOrderAxisGradientMajorantDensity
        u t i k l j zAxis x
  )

/--
The full twelve-term `D³u · Du` gradient block is pointwise controlled by the
velocity-gradient envelope.
-/
theorem thirdTransportCommutatorGradientBlock_density_le_gradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {t : ℝ}
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (i k l j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    2
        *
      abs
        (
          spatial3.d i
              (
                spatial3.d k
                  (
                    spatial3.d l
                      (loggedVelocityComponent u t j)
                  )
              )
              x
            *
          thirdTransportCommutatorGradientBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j x
        )
      ≤
    h t
      *
    thirdOrderGradientMajorantDensity
      u t i k l j x := by

  let f : ℝ :=
    spatial3.d i
      (
        spatial3.d k
          (
            spatial3.d l
              (loggedVelocityComponent u t j)
          )
      )
      x

  let gx : ℝ :=
    thirdTransportCommutatorAxisGradientBlock
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t i k l j xAxis x

  let gy : ℝ :=
    thirdTransportCommutatorAxisGradientBlock
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t i k l j yAxis x

  let gz : ℝ :=
    thirdTransportCommutatorAxisGradientBlock
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          u
      )
      t i k l j zAxis x

  let mx : ℝ :=
    thirdOrderAxisGradientMajorantDensity
      u t i k l j xAxis x

  let my : ℝ :=
    thirdOrderAxisGradientMajorantDensity
      u t i k l j yAxis x

  let mz : ℝ :=
    thirdOrderAxisGradientMajorantDensity
      u t i k l j zAxis x

  have hx :
      2 * |f * gx|
        ≤
      h t * mx := by

    dsimp [f, gx, mx]

    exact
      thirdTransportCommutatorAxisGradientBlock_density_le_gradientEnvelope
        hGradient
        i k l j xAxis x

  have hy :
      2 * |f * gy|
        ≤
      h t * my := by

    dsimp [f, gy, my]

    exact
      thirdTransportCommutatorAxisGradientBlock_density_le_gradientEnvelope
        hGradient
        i k l j yAxis x

  have hz :
      2 * |f * gz|
        ≤
      h t * mz := by

    dsimp [f, gz, mz]

    exact
      thirdTransportCommutatorAxisGradientBlock_density_le_gradientEnvelope
        hGradient
        i k l j zAxis x

  have hCombined :
      2 * |f * (gx + (gy + gz))|
        ≤
      h t * (mx + (my + mz)) :=
    three_gradient_blocks_algebra_bound
      hx hy hz

  dsimp
    [
      f,
      gx,
      gy,
      gz,
      mx,
      my,
      mz
    ]
    at hCombined

  simpa
    [
      thirdTransportCommutatorGradientBlock,
      thirdOrderGradientMajorantDensity
    ]
    using hCombined

end Euclidean
end Bridge
end PrimeTensor
