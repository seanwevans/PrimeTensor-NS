import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three

/-!
# Direct pointwise bound for the first H³ transport commutator

The exact transport decomposition/cancellation is now green through derivative
orders zero, one, two, and three.

This file begins the actual estimate.  The first commutator is elementary:

    C₁(i,j)
      =
    (∂ᵢvₓ)(∂ₓvⱼ)
      +
    (∂ᵢvᵧ)(∂ᵧvⱼ)
      +
    (∂ᵢv_z)(∂_zvⱼ).

If `h` bounds every first velocity derivative, then one factor in each product
is bounded by `h`.  Young's inequality

    2 |ab| ≤ a² + b²

therefore gives the pointwise estimate

    2 |(∂ᵢvⱼ) C₁(i,j)|
      ≤
    h [
      3 (∂ᵢvⱼ)²
        + (∂ₓvⱼ)²
        + (∂ᵧvⱼ)²
        + (∂_zvⱼ)²
    ].

This is precisely the form needed for the subsequent integral estimate: the
right-hand side contains only first-order square-energy densities and no
spatially constant term.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open MeasureTheory

/-! ## Pure real algebra -/

/--
One bounded factor plus Young's inequality controls a triple product.
-/
private theorem two_abs_triple_mul_le
    {H a b c : ℝ}
    (
      ha :
        |a| ≤ H
    ) :
    2 * |c * (a * b)|
      ≤
    H * (c ^ 2 + b ^ 2) := by

  have hH :
      0 ≤ H :=
    le_trans
      (abs_nonneg a)
      ha

  have hYoungAbs :
      2 * |c| * |b|
        ≤
      |c| ^ 2 + |b| ^ 2 := by

    nlinarith
      [
        sq_nonneg
          (|c| - |b|)
      ]

  have hYoung :
      2 * |c| * |b|
        ≤
      c ^ 2 + b ^ 2 := by

    simpa only [sq_abs] using hYoungAbs

  have hScaleA :
      |a| * (2 * |c| * |b|)
        ≤
      H * (2 * |c| * |b|) := by

    exact
      mul_le_mul_of_nonneg_right
        ha
        (by positivity)

  have hScaleYoung :
      H * (2 * |c| * |b|)
        ≤
      H * (c ^ 2 + b ^ 2) := by

    exact
      mul_le_mul_of_nonneg_left
        hYoung
        hH

  calc
    2 * |c * (a * b)|
        =
      |a| * (2 * |c| * |b|) := by
        rw [
          abs_mul,
          abs_mul
        ]
        ring
    _ ≤ H * (2 * |c| * |b|) :=
      hScaleA
    _ ≤ H * (c ^ 2 + b ^ 2) :=
      hScaleYoung

/--
Three bounded coefficient factors control the first commutator density.
-/
private theorem first_commutator_algebra_bound
    {H f ax ay az bx byv bz : ℝ}
    (
      hax :
        |ax| ≤ H
    )
    (
      hay :
        |ay| ≤ H
    )
    (
      haz :
        |az| ≤ H
    ) :
    2
        *
      abs
        (
          f
            *
          (
            ax * bx
              +
            (
              ay * byv
                +
              az * bz
            )
          )
        )
      ≤
    H
      *
    (
      3 * f ^ 2
        +
      (
        bx ^ 2
          +
        (
          byv ^ 2
            +
          bz ^ 2
        )
      )
    ) := by

  have hx :
      2 * |f * (ax * bx)|
        ≤
      H * (f ^ 2 + bx ^ 2) :=
    two_abs_triple_mul_le
      (a := ax)
      (b := bx)
      (c := f)
      hax

  have hy :
      2 * |f * (ay * byv)|
        ≤
      H * (f ^ 2 + byv ^ 2) :=
    two_abs_triple_mul_le
      (a := ay)
      (b := byv)
      (c := f)
      hay

  have hz :
      2 * |f * (az * bz)|
        ≤
      H * (f ^ 2 + bz ^ 2) :=
    two_abs_triple_mul_le
      (a := az)
      (b := bz)
      (c := f)
      haz

  have hAbs :
      abs
        (
          f
            *
          (
            ax * bx
              +
            (
              ay * byv
                +
              az * bz
            )
          )
        )
        ≤
      |f * (ax * bx)|
        +
      (
        |f * (ay * byv)|
          +
        |f * (az * bz)|
      ) := by

    have hRewrite :
        f
            *
          (
            ax * bx
              +
            (
              ay * byv
                +
              az * bz
            )
          )
          =
        f * (ax * bx)
          +
        (
          f * (ay * byv)
            +
          f * (az * bz)
        ) := by

      ring

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
      2
          *
        abs
          (
            f
              *
            (
              ax * bx
                +
              (
                ay * byv
                  +
                az * bz
              )
            )
          )
        ≤
      2
        *
      (
        |f * (ax * bx)|
          +
        (
          |f * (ay * byv)|
            +
          |f * (az * bz)|
        )
      ) := by

    exact
      mul_le_mul_of_nonneg_left
        hAbs
        (by norm_num)

  nlinarith

/-! ## Logged velocity specialization -/

/--
The first transport commutator density is pointwise controlled by the
velocity-gradient envelope and first-order square-energy densities.
-/
theorem firstTransportCommutator_density_le_gradientEnvelope
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
    (i j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    2
        *
      abs
        (
          spatial3.d
              i
              (loggedVelocityComponent u t j)
              x
            *
          firstTransportCommutator
              (
                PrimeTensor.Bridge.logSpaceTimeVectorField
                  u
              )
              t i j x
        )
      ≤
    h t
      *
    (
      3
          *
        (
          spatial3.d
              i
              (loggedVelocityComponent u t j)
              x
        ) ^ 2
        +
      (
        (
          spatial3.d
              xAxis
              (loggedVelocityComponent u t j)
              x
        ) ^ 2
          +
        (
          (
            spatial3.d
                yAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
            +
          (
            spatial3.d
                zAxis
                (loggedVelocityComponent u t j)
                x
          ) ^ 2
        )
      )
    ) := by

  have hax :
      abs
        (
          spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component xAxis
              )
              x
        )
        ≤
      h t :=
    hGradient
      i xAxis x

  have hay :
      abs
        (
          spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component yAxis
              )
              x
        )
        ≤
      h t :=
    hGradient
      i yAxis x

  have haz :
      abs
        (
          spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component zAxis
              )
              x
        )
        ≤
      h t :=
    hGradient
      i zAxis x

  change
    2
        *
      abs
        (
          spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
            *
          (
            spatial3.d
                i
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
              *
            spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component j
                )
                x
              +
            (
              spatial3.d
                  i
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component yAxis
                  )
                  x
                *
              spatial3.d
                  yAxis
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  x
                +
              spatial3.d
                  i
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component zAxis
                  )
                  x
                *
              spatial3.d
                  zAxis
                  (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  x
            )
          )
        )
      ≤
    h t
      *
    (
      3
          *
        (
          spatial3.d
              i
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
        ) ^ 2
        +
      (
        (
          spatial3.d
              xAxis
              (
                fun y =>
                  (
                    PrimeTensor.Bridge.logSpaceTimeVectorField
                      u t y
                  ).component j
              )
              x
        ) ^ 2
          +
        (
          (
            spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component j
                )
                x
          ) ^ 2
            +
          (
            spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component j
                )
                x
          ) ^ 2
        )
      )
    )

  exact
    first_commutator_algebra_bound
      (H := h t)
      (
        f :=
          spatial3.d
            i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
            x
      )
      (
        ax :=
          spatial3.d
            i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component xAxis
            )
            x
      )
      (
        ay :=
          spatial3.d
            i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component yAxis
            )
            x
      )
      (
        az :=
          spatial3.d
            i
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component zAxis
            )
            x
      )
      (
        bx :=
          spatial3.d
            xAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
            x
      )
      (
        byv :=
          spatial3.d
            yAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
            x
      )
      (
        bz :=
          spatial3.d
            zAxis
            (
              fun y =>
                (
                  PrimeTensor.Bridge.logSpaceTimeVectorField
                    u t y
                ).component j
            )
            x
      )
      hax hay haz

/--
A velocity-gradient envelope is necessarily nonnegative at the time at which
it is an envelope.
-/
theorem velocityGradientEnvelope_nonneg
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
    (x : Point3) :
    0 ≤ h t := by

  exact
    le_trans
      (
        abs_nonneg
          (
            spatial3.d
              xAxis
              (loggedVelocityComponent u t xAxis)
              x
          )
      )
      (
        hGradient
          xAxis xAxis x
      )

end Euclidean
end Bridge
end PrimeTensor
