import PrimeTensor.Fluid.VorticityH3EnergyTransportOrderTwoExpansion

/-!
# Pointwise second-order H³ transport commutator bound

The explicit order-two commutator has three coordinate groups.  In each group
there are three products, and every product contains exactly one first
derivative and one second derivative.  Pairing with `∂ᵢ∂ₖvⱼ` therefore yields
nine cubic terms of the form

    F * (A * B),

where `|A| ≤ h(t)` by the velocity-gradient envelope and both `F` and `B`
are second derivatives.

Young's inequality gives

    2 |F (A B)| ≤ h(t) (F² + B²).

Summing the nine terms gives the pointwise order-two majorant used by the next
integration module.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

noncomputable local instance axisFintypeH3EnergyTransportOrderTwoBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-! ## Scalar algebra -/

private theorem two_abs_triple_mul_le_orderTwo
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

private theorem three_term_algebra_bound_orderTwo
    {H f a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
    (
      ha₁ :
        |a₁| ≤ H
    )
    (
      ha₂ :
        |a₂| ≤ H
    )
    (
      ha₃ :
        |a₃| ≤ H
    ) :
    2
        *
      abs
        (
          f
            *
          (
            b₁ * a₁
              +
            (
              a₂ * b₂
                +
              a₃ * b₃
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
        b₁ ^ 2
          +
        (
          b₂ ^ 2
            +
          b₃ ^ 2
        )
      )
    ) := by

  have h₁ :
      2 * |f * (b₁ * a₁)|
        ≤
      H * (f ^ 2 + b₁ ^ 2) :=
    by
      simpa [mul_comm] using
        (
          two_abs_triple_mul_le_orderTwo
            (a := a₁)
            (b := b₁)
            (c := f)
            ha₁
        )

  have h₂ :
      2 * |f * (a₂ * b₂)|
        ≤
      H * (f ^ 2 + b₂ ^ 2) :=
    two_abs_triple_mul_le_orderTwo
      (a := a₂)
      (b := b₂)
      (c := f)
      ha₂

  have h₃ :
      2 * |f * (a₃ * b₃)|
        ≤
      H * (f ^ 2 + b₃ ^ 2) :=
    two_abs_triple_mul_le_orderTwo
      (a := a₃)
      (b := b₃)
      (c := f)
      ha₃

  have hAbs :
      abs
        (
          f
            *
          (
            b₁ * a₁
              +
            (
              a₂ * b₂
                +
              a₃ * b₃
            )
          )
        )
        ≤
      |f * (b₁ * a₁)|
        +
      (
        |f * (a₂ * b₂)|
          +
        |f * (a₃ * b₃)|
      ) := by

    have hRewrite :
        f
            *
          (
            b₁ * a₁
              +
            (
              a₂ * b₂
                +
              a₃ * b₃
            )
          )
          =
        f * (b₁ * a₁)
          +
        (
          f * (a₂ * b₂)
            +
          f * (a₃ * b₃)
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
              b₁ * a₁
                +
              (
                a₂ * b₂
                  +
                a₃ * b₃
              )
            )
          )
        ≤
      2
        *
      (
        |f * (b₁ * a₁)|
          +
        (
          |f * (a₂ * b₂)|
            +
          |f * (a₃ * b₃)|
        )
      ) := by

    exact
      mul_le_mul_of_nonneg_left
        hAbs
        (by norm_num)

  nlinarith

private theorem nine_term_algebra_bound_orderTwo
    {
      H f
      ax₁ ax₂ ax₃
      ay₁ ay₂ ay₃
      az₁ az₂ az₃
      bx₁ bx₂ bx₃
      by₁ by₂ by₃
      bz₁ bz₂ bz₃ :
        ℝ
    }
    (hax₁ : |ax₁| ≤ H)
    (hax₂ : |ax₂| ≤ H)
    (hax₃ : |ax₃| ≤ H)
    (hay₁ : |ay₁| ≤ H)
    (hay₂ : |ay₂| ≤ H)
    (hay₃ : |ay₃| ≤ H)
    (haz₁ : |az₁| ≤ H)
    (haz₂ : |az₂| ≤ H)
    (haz₃ : |az₃| ≤ H) :
    2
        *
      abs
        (
          f
            *
          (
            (
              bx₁ * ax₁
                +
              (
                ax₂ * bx₂
                  +
                ax₃ * bx₃
              )
            )
              +
            (
              (
                by₁ * ay₁
                  +
                (
                  ay₂ * by₂
                    +
                  ay₃ * by₃
                )
              )
                +
              (
                bz₁ * az₁
                  +
                (
                  az₂ * bz₂
                    +
                  az₃ * bz₃
                )
              )
            )
          )
        )
      ≤
    H
      *
    (
      9 * f ^ 2
        +
      (
        (
          bx₁ ^ 2
            +
          (
            bx₂ ^ 2
              +
            bx₃ ^ 2
          )
        )
          +
        (
          (
            by₁ ^ 2
              +
            (
              by₂ ^ 2
                +
              by₃ ^ 2
            )
          )
            +
          (
            bz₁ ^ 2
              +
            (
              bz₂ ^ 2
                +
              bz₃ ^ 2
            )
          )
        )
      )
    ) := by

  have hx :
      2
          *
        abs
          (
            f
              *
            (
              bx₁ * ax₁
                +
              (
                ax₂ * bx₂
                  +
                ax₃ * bx₃
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
          bx₁ ^ 2
            +
          (
            bx₂ ^ 2
              +
            bx₃ ^ 2
          )
        )
      ) :=
    three_term_algebra_bound_orderTwo
      hax₁ hax₂ hax₃

  have hy :
      2
          *
        abs
          (
            f
              *
            (
              by₁ * ay₁
                +
              (
                ay₂ * by₂
                  +
                ay₃ * by₃
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
          by₁ ^ 2
            +
          (
            by₂ ^ 2
              +
            by₃ ^ 2
          )
        )
      ) :=
    three_term_algebra_bound_orderTwo
      hay₁ hay₂ hay₃

  have hz :
      2
          *
        abs
          (
            f
              *
            (
              bz₁ * az₁
                +
              (
                az₂ * bz₂
                  +
                az₃ * bz₃
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
          bz₁ ^ 2
            +
          (
            bz₂ ^ 2
              +
            bz₃ ^ 2
          )
        )
      ) :=
    three_term_algebra_bound_orderTwo
      haz₁ haz₂ haz₃

  have hAbs :
      abs
        (
          f
            *
          (
            (
              bx₁ * ax₁
                +
              (
                ax₂ * bx₂
                  +
                ax₃ * bx₃
              )
            )
              +
            (
              (
                by₁ * ay₁
                  +
                (
                  ay₂ * by₂
                    +
                  ay₃ * by₃
                )
              )
                +
              (
                bz₁ * az₁
                  +
                (
                  az₂ * bz₂
                    +
                  az₃ * bz₃
                )
              )
            )
          )
        )
        ≤
      abs
        (
          f
            *
          (
            bx₁ * ax₁
              +
            (
              ax₂ * bx₂
                +
              ax₃ * bx₃
            )
          )
        )
        +
      (
        abs
          (
            f
              *
            (
              by₁ * ay₁
                +
              (
                ay₂ * by₂
                  +
                ay₃ * by₃
              )
            )
          )
          +
        abs
          (
            f
              *
            (
              bz₁ * az₁
                +
              (
                az₂ * bz₂
                  +
                az₃ * bz₃
              )
            )
          )
      ) := by

    have hRewrite :
        f
            *
          (
            (
              bx₁ * ax₁
                +
              (
                ax₂ * bx₂
                  +
                ax₃ * bx₃
              )
            )
              +
            (
              (
                by₁ * ay₁
                  +
                (
                  ay₂ * by₂
                    +
                  ay₃ * by₃
                )
              )
                +
              (
                bz₁ * az₁
                  +
                (
                  az₂ * bz₂
                    +
                  az₃ * bz₃
                )
              )
            )
          )
          =
        f
            *
          (
            bx₁ * ax₁
              +
            (
              ax₂ * bx₂
                +
              ax₃ * bx₃
            )
          )
          +
        (
          f
              *
            (
              by₁ * ay₁
                +
              (
                ay₂ * by₂
                  +
                ay₃ * by₃
              )
            )
            +
          f
              *
            (
              bz₁ * az₁
                +
              (
                az₂ * bz₂
                  +
                az₃ * bz₃
              )
            )
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
              (
                bx₁ * ax₁
                  +
                (
                  ax₂ * bx₂
                    +
                  ax₃ * bx₃
                )
              )
                +
              (
                (
                  by₁ * ay₁
                    +
                  (
                    ay₂ * by₂
                      +
                    ay₃ * by₃
                  )
                )
                  +
                (
                  bz₁ * az₁
                    +
                  (
                    az₂ * bz₂
                      +
                    az₃ * bz₃
                  )
                )
              )
            )
          )
        ≤
      2
        *
      (
        abs
          (
            f
              *
            (
              bx₁ * ax₁
                +
              (
                ax₂ * bx₂
                  +
                ax₃ * bx₃
              )
            )
          )
          +
        (
          abs
            (
              f
                *
              (
                by₁ * ay₁
                  +
                (
                  ay₂ * by₂
                    +
                  ay₃ * by₃
                )
              )
            )
            +
          abs
            (
              f
                *
              (
                bz₁ * az₁
                  +
                (
                  az₂ * bz₂
                    +
                  az₃ * bz₃
                )
              )
            )
        )
      ) := by

    exact
      mul_le_mul_of_nonneg_left
        hAbs
        (by norm_num)

  nlinarith

/-! ## Logged velocity specialization -/

/--
The quadratic second-derivative density appearing in the pointwise order-two
commutator estimate.
-/
noncomputable def secondOrderCommutatorMajorantDensity
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (i k j : PrimeTensor.Axis Depth.three)
    (x : Point3) : ℝ :=
  9
      *
    (
      spatial3.d
        i
        (
          spatial3.d
            k
            (loggedVelocityComponent u t j)
        )
        x
    ) ^ 2
    +
  (
    (
      (
        spatial3.d
          i
          (
            spatial3.d
              k
              (loggedVelocityComponent u t xAxis)
          )
          x
      ) ^ 2
        +
      (
        (
          spatial3.d
            i
            (
              spatial3.d
                xAxis
                (loggedVelocityComponent u t j)
            )
            x
        ) ^ 2
          +
        (
          spatial3.d
            xAxis
            (
              spatial3.d
                k
                (loggedVelocityComponent u t j)
            )
            x
        ) ^ 2
      )
    )
      +
    (
      (
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t yAxis)
            )
            x
        ) ^ 2
          +
        (
          (
            spatial3.d
              i
              (
                spatial3.d
                  yAxis
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
            +
          (
            spatial3.d
              yAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
        )
      )
        +
      (
        (
          spatial3.d
            i
            (
              spatial3.d
                k
                (loggedVelocityComponent u t zAxis)
            )
            x
        ) ^ 2
          +
        (
          (
            spatial3.d
              i
              (
                spatial3.d
                  zAxis
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
            +
          (
            spatial3.d
              zAxis
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
          ) ^ 2
        )
      )
    )
  )

/--
The exposed order-two commutator density is controlled pointwise by the
velocity-gradient envelope and the explicit quadratic second-derivative
majorant.
-/
theorem secondTransportCommutatorExpanded_density_le_gradientEnvelope
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
    (i k j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    2
        *
      abs
        (
          spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
            *
          secondTransportCommutatorExpanded
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j x
        )
      ≤
    h t
      *
    secondOrderCommutatorMajorantDensity
      u t i k j x := by

  have hx₁ :
      abs
        (
          spatial3.d
            xAxis
            (loggedVelocityComponent u t j)
            x
        )
        ≤
      h t :=
    hGradient xAxis j x

  have hx₂ :
      abs
        (
          spatial3.d
            k
            (loggedVelocityComponent u t xAxis)
            x
        )
        ≤
      h t :=
    hGradient k xAxis x

  have hx₃ :
      abs
        (
          spatial3.d
            i
            (loggedVelocityComponent u t xAxis)
            x
        )
        ≤
      h t :=
    hGradient i xAxis x

  have hy₁ :
      abs
        (
          spatial3.d
            yAxis
            (loggedVelocityComponent u t j)
            x
        )
        ≤
      h t :=
    hGradient yAxis j x

  have hy₂ :
      abs
        (
          spatial3.d
            k
            (loggedVelocityComponent u t yAxis)
            x
        )
        ≤
      h t :=
    hGradient k yAxis x

  have hy₃ :
      abs
        (
          spatial3.d
            i
            (loggedVelocityComponent u t yAxis)
            x
        )
        ≤
      h t :=
    hGradient i yAxis x

  have hz₁ :
      abs
        (
          spatial3.d
            zAxis
            (loggedVelocityComponent u t j)
            x
        )
        ≤
      h t :=
    hGradient zAxis j x

  have hz₂ :
      abs
        (
          spatial3.d
            k
            (loggedVelocityComponent u t zAxis)
            x
        )
        ≤
      h t :=
    hGradient k zAxis x

  have hz₃ :
      abs
        (
          spatial3.d
            i
            (loggedVelocityComponent u t zAxis)
            x
        )
        ≤
      h t :=
    hGradient i zAxis x

  unfold
    secondTransportCommutatorExpanded
    secondOrderCommutatorMajorantDensity

  have hComponent :
      ∀ r : PrimeTensor.Axis Depth.three,
        loggedVelocityComponent u t r
          =
        (
          fun y =>
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u t y
            ).component r
        ) := by

    intro r
    rfl

  rw [
    hComponent j,
    hComponent xAxis,
    hComponent yAxis,
    hComponent zAxis
  ]

  simpa only [add_assoc] using
    (
      nine_term_algebra_bound_orderTwo
            (H := h t)
            (
              f :=
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  )
                  x
            )
            (
              ax₁ :=
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
              ax₂ :=
                spatial3.d
                  k
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
              ax₃ :=
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
              ay₁ :=
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
              ay₂ :=
                spatial3.d
                  k
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
              ay₃ :=
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
              az₁ :=
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
            (
              az₂ :=
                spatial3.d
                  k
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
              az₃ :=
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
              bx₁ :=
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component xAxis
                  )
                  )
                  x
            )
            (
              bx₂ :=
                spatial3.d
                  i
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
                  )
                  x
            )
            (
              bx₃ :=
                spatial3.d
                  xAxis
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  )
                  x
            )
            (
              by₁ :=
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component yAxis
                  )
                  )
                  x
            )
            (
              by₂ :=
                spatial3.d
                  i
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
                  )
                  x
            )
            (
              by₃ :=
                spatial3.d
                  yAxis
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  )
                  x
            )
            (
              bz₁ :=
                spatial3.d
                  i
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component zAxis
                  )
                  )
                  x
            )
            (
              bz₂ :=
                spatial3.d
                  i
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
                  )
                  x
            )
            (
              bz₃ :=
                spatial3.d
                  zAxis
                  (
                    spatial3.d
                      k
                      (
                    fun y =>
                      (
                        PrimeTensor.Bridge.logSpaceTimeVectorField
                          u t y
                      ).component j
                  )
                  )
                  x
            )
            hx₁ hx₂ hx₃
            hy₁ hy₂ hy₃
            hz₁ hz₂ hz₃
    )

/--
The actual second transport commutator satisfies the same pointwise bound on
a strict preterminal H³-energy-class time slice.
-/
theorem secondTransportCommutator_density_le_gradientEnvelope
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {h : ℝ → ℝ}
    {a T t : ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      ht :
        t ∈ Set.Ioo a T
    )
    (
      hGradient :
        VelocityGradientEnvelope
          u h t
    )
    (i k j : PrimeTensor.Axis Depth.three)
    (x : Point3) :
    2
        *
      abs
        (
          spatial3.d
              i
              (
                spatial3.d
                  k
                  (loggedVelocityComponent u t j)
              )
              x
            *
          secondTransportCommutator
            (
              PrimeTensor.Bridge.logSpaceTimeVectorField
                u
            )
            t i k j x
        )
      ≤
    h t
      *
    secondOrderCommutatorMajorantDensity
      u t i k j x := by

  rcases
      hClass.pressure_witness
    with
      ⟨p, s, hp4⟩

  have htNS :
      t ∈ Set.Ioo (0 : ℝ) T :=
    ⟨
      lt_trans
        hClass.terminal_start.1
        ht.1,
      ht.2
    ⟩

  rw [
    secondTransportCommutator_eq_expanded
      s htNS x i k j
  ]

  exact
    secondTransportCommutatorExpanded_density_le_gradientEnvelope
      hGradient
      i k j x

end Euclidean
end Bridge
end PrimeTensor
