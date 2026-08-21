import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Split

/-!
# Third-order H³ transport: axis-local gradient-envelope bound

This file estimates only the easy `D³u · Du` part of the third-order
commutator.  For one velocity axis `r`, the gradient block has four terms.
After pairing with the distinguished third derivative `f`, each term contains
one first derivative controlled by `VelocityGradientEnvelope`.

Young's inequality gives the pointwise estimate

    2 |f G_r|
      ≤ h(t) (4 f² + b₁² + b₂² + b₃² + b₄²).

The genuinely new `D²u · D²u` interpolation block is not touched here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
One bounded coefficient plus Young's inequality controls a triple product.
-/
private theorem two_abs_triple_mul_le_orderThreeGradient
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
Four bounded first-derivative coefficients control one axis of the top-order
gradient block.
-/
private theorem four_gradient_terms_algebra_bound
    {
      H f
      a1 a2 a3 a4
      b1 b2 b3 b4 : ℝ
    }
    (ha1 : |a1| ≤ H)
    (ha2 : |a2| ≤ H)
    (ha3 : |a3| ≤ H)
    (ha4 : |a4| ≤ H) :
    2
        *
      abs
        (
          f
            *
          (
            a1 * b1
              +
            a2 * b2
              +
            a3 * b3
              +
            a4 * b4
          )
        )
      ≤
    H
      *
    (
      4 * f ^ 2
        +
      b1 ^ 2
        +
      b2 ^ 2
        +
      b3 ^ 2
        +
      b4 ^ 2
    ) := by

  have h1 :
      2 * |f * (a1 * b1)|
        ≤
      H * (f ^ 2 + b1 ^ 2) :=
    two_abs_triple_mul_le_orderThreeGradient
      (a := a1)
      (b := b1)
      (c := f)
      ha1

  have h2 :
      2 * |f * (a2 * b2)|
        ≤
      H * (f ^ 2 + b2 ^ 2) :=
    two_abs_triple_mul_le_orderThreeGradient
      (a := a2)
      (b := b2)
      (c := f)
      ha2

  have h3 :
      2 * |f * (a3 * b3)|
        ≤
      H * (f ^ 2 + b3 ^ 2) :=
    two_abs_triple_mul_le_orderThreeGradient
      (a := a3)
      (b := b3)
      (c := f)
      ha3

  have h4 :
      2 * |f * (a4 * b4)|
        ≤
      H * (f ^ 2 + b4 ^ 2) :=
    two_abs_triple_mul_le_orderThreeGradient
      (a := a4)
      (b := b4)
      (c := f)
      ha4

  have hRewrite :
      f
          *
        (
          a1 * b1
            +
          a2 * b2
            +
          a3 * b3
            +
          a4 * b4
        )
        =
      (
        (
          f * (a1 * b1)
            +
          f * (a2 * b2)
        )
          +
        f * (a3 * b3)
      )
        +
      f * (a4 * b4) := by
    ring

  have hAbs :
      abs
        (
          f
            *
          (
            a1 * b1
              +
            a2 * b2
              +
            a3 * b3
              +
            a4 * b4
          )
        )
        ≤
      (
        (
          |f * (a1 * b1)|
            +
          |f * (a2 * b2)|
        )
          +
        |f * (a3 * b3)|
      )
        +
      |f * (a4 * b4)| := by

    rw [hRewrite]

    calc
      abs
          (
            (
              (
                f * (a1 * b1)
                  +
                f * (a2 * b2)
              )
                +
              f * (a3 * b3)
            )
              +
            f * (a4 * b4)
          )
          ≤
        abs
            (
              (
                f * (a1 * b1)
                  +
                f * (a2 * b2)
              )
                +
              f * (a3 * b3)
            )
          +
        |f * (a4 * b4)| :=
        abs_add_le _ _
      _ ≤
        (
          |f * (a1 * b1)|
            +
          |f * (a2 * b2)|
        )
          +
        |f * (a3 * b3)|
          +
        |f * (a4 * b4)| := by

        have h12 :
            abs
                (
                  f * (a1 * b1)
                    +
                  f * (a2 * b2)
                )
              ≤
            |f * (a1 * b1)|
              +
            |f * (a2 * b2)| :=
          abs_add_le _ _

        have h123 :
            abs
                (
                  (
                    f * (a1 * b1)
                      +
                    f * (a2 * b2)
                  )
                    +
                  f * (a3 * b3)
                )
              ≤
            (
              |f * (a1 * b1)|
                +
              |f * (a2 * b2)|
            )
              +
            |f * (a3 * b3)| :=
          le_trans
            (abs_add_le _ _)
            (
              add_le_add_left
                h12
                _
            )

        exact
          add_le_add_left
            h123
            _

  have hAbsTwo :
      2
          *
        abs
          (
            f
              *
            (
              a1 * b1
                +
              a2 * b2
                +
              a3 * b3
                +
              a4 * b4
            )
          )
        ≤
      2
        *
      (
        (
          |f * (a1 * b1)|
            +
          |f * (a2 * b2)|
        )
          +
        |f * (a3 * b3)|
          +
        |f * (a4 * b4)|
      ) := by

    exact
      mul_le_mul_of_nonneg_left
        hAbs
        (by norm_num)

  nlinarith

/--
The square-density majorant for one coordinate-axis gradient block.
-/
noncomputable def thirdOrderAxisGradientMajorantDensity
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k l j r : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  let f :=
    spatial3.d i
      (spatial3.d k
        (spatial3.d l
          (loggedVelocityComponent u t j))) x
  let b1 :=
    spatial3.d i
      (spatial3.d k
        (spatial3.d l
          (loggedVelocityComponent u t r))) x
  let b2 :=
    spatial3.d i
      (spatial3.d k
        (spatial3.d r
          (loggedVelocityComponent u t j))) x
  let b3 :=
    spatial3.d i
      (spatial3.d r
        (spatial3.d l
          (loggedVelocityComponent u t j))) x
  let b4 :=
    spatial3.d r
      (spatial3.d k
        (spatial3.d l
          (loggedVelocityComponent u t j))) x
  4 * f ^ 2
    + b1 ^ 2
    + b2 ^ 2
    + b3 ^ 2
    + b4 ^ 2

/--
One coordinate-axis `D³u · Du` block is controlled pointwise by the
velocity-gradient envelope.
-/
theorem thirdTransportCommutatorAxisGradientBlock_density_le_gradientEnvelope
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
    (i k l j r : PrimeTensor.Axis Depth.three)
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
          thirdTransportCommutatorAxisGradientBlock
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k l j r x
        )
      ≤
    h t
      *
    thirdOrderAxisGradientMajorantDensity
      u t i k l j r x := by

  have ha1 :
      abs
        (
          spatial3.d
            r
            (loggedVelocityComponent u t j)
            x
        )
        ≤
      h t :=
    hGradient r j x

  have ha2 :
      abs
        (
          spatial3.d
            l
            (loggedVelocityComponent u t r)
            x
        )
        ≤
      h t :=
    hGradient l r x

  have ha3 :
      abs
        (
          spatial3.d
            k
            (loggedVelocityComponent u t r)
            x
        )
        ≤
      h t :=
    hGradient k r x

  have ha4 :
      abs
        (
          spatial3.d
            i
            (loggedVelocityComponent u t r)
            x
        )
        ≤
      h t :=
    hGradient i r x

  have hComponent :
      ∀ q : PrimeTensor.Axis Depth.three,
        (
          fun y : Point3 =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component q
        )
          =
        loggedVelocityComponent u t q := by

    intro q
    rfl

  unfold
    thirdTransportCommutatorAxisGradientBlock
    thirdOrderAxisGradientMajorantDensity

  rw [
    hComponent j,
    hComponent r
  ]

  simpa only
    [
      mul_comm,
      mul_left_comm,
      mul_assoc,
      add_assoc
    ]
    using
      (
        four_gradient_terms_algebra_bound
          (H := h t)
          (
            f :=
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
          )
          (
            a1 :=
              spatial3.d r
                (loggedVelocityComponent u t j)
                x
          )
          (
            a2 :=
              spatial3.d l
                (loggedVelocityComponent u t r)
                x
          )
          (
            a3 :=
              spatial3.d k
                (loggedVelocityComponent u t r)
                x
          )
          (
            a4 :=
              spatial3.d i
                (loggedVelocityComponent u t r)
                x
          )
          (
            b1 :=
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t r)
                    )
                )
                x
          )
          (
            b2 :=
              spatial3.d i
                (
                  spatial3.d k
                    (
                      spatial3.d r
                        (loggedVelocityComponent u t j)
                    )
                )
                x
          )
          (
            b3 :=
              spatial3.d i
                (
                  spatial3.d r
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
          )
          (
            b4 :=
              spatial3.d r
                (
                  spatial3.d k
                    (
                      spatial3.d l
                        (loggedVelocityComponent u t j)
                    )
                )
                x
          )
          ha1 ha2 ha3 ha4
      )

end Euclidean
end Bridge
end PrimeTensor
