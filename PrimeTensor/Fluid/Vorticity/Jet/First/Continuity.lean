import PrimeTensor.Fluid.Vorticity.Time.Continuity

/-!
# First-jet time continuity for the moving-time vorticity cascade

`VorticityTimeContinuity` isolates a six-channel continuity assumption for the
primitive inputs to vortex stretching:

    ωₓ, ∂ₓuⱼ, ωᵧ, ∂ᵧuⱼ, ω_z, ∂_zuⱼ.

Those six channels are not independent.  In logarithmic coordinates every
native velocity-gradient input is one entry of the ordinary spatial first jet
of the logged velocity field, while every vorticity component is a difference
of two entries of that same first jet.

This file therefore introduces a single first-jet continuity predicate:

    for every spatial direction i and velocity component j,
    t ↦ ∂ᵢ (log uⱼ)(t,x)

is continuous at T.

The existing logarithmic derivative compatibility and vorticity semantics then
derive the six primitive continuity hypotheses automatically.

This is still only a continuation interface.  It does not prove that a
Navier--Stokes solution has such terminal first-jet continuity, nor does it
derive the vorticity second-jet convergence needed by the diffusion branch.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
Time continuity at `(T,x)` of the complete spatial first jet of the logged
velocity field.
-/
def VelocityFirstJetLogContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀ (i j : PrimeTensor.Axis Depth.three),
    ContinuousAt
      (
        fun t =>
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
      T

/--
One native velocity-gradient logarithm is continuous in time whenever the
corresponding entry of the logged first jet is continuous.
-/
theorem velocityGradientLogContinuousAt_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    )
    (i j : PrimeTensor.Axis Depth.three) :
    ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulSpatial3.d
                i
                (fun y => (u t y).component j)
                x
            )
      )
      T := by

  have hEntry :=
    hJet i j

  have hFunctions :
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulSpatial3.d
                i
                (fun y => (u t y).component j)
                x
            )
      )
        =
      (
        fun t =>
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
      ) := by

    funext t

    have hLog :=
      PrimeTensor.Bridge.Euclidean.mulSpatial3_compatible.d_log
        i
        (fun y => (u t y).component j)
        x

    simpa [
      PrimeTensor.Bridge.logSpaceTimeVectorField,
      PrimeTensor.Bridge.logVectorField
    ] using hLog.symm

  rw [hFunctions]

  exact hEntry

/--
The x-vorticity logarithm is continuous in time when the logged first jet is
continuous.
-/
theorem vorticityXLogContinuousAt_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityX u t x)
      )
      T := by

  have hReal :
      ContinuousAt
        (
          fun t =>
            realVorticityX
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        T := by

    have hSub :=
      (hJet yAxis zAxis).sub
        (hJet zAxis yAxis)

    have hPointwise :
        (
          (
            fun t =>
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
          )
            -
          (
            fun t =>
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
          )
        )
          =
        (
          fun t =>
            spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
              -
            spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
        ) := by

      funext t
      rfl

    rw [hPointwise] at hSub

    simpa only [
      realVorticityX
    ] using hSub

  simpa only [
    logValue_mulVorticityX
  ] using hReal

/--
The y-vorticity logarithm is continuous in time when the logged first jet is
continuous.
-/
theorem vorticityYLogContinuousAt_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityY u t x)
      )
      T := by

  have hReal :
      ContinuousAt
        (
          fun t =>
            realVorticityY
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        T := by

    have hSub :=
      (hJet zAxis xAxis).sub
        (hJet xAxis zAxis)

    have hPointwise :
        (
          (
            fun t =>
              spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
          )
            -
          (
            fun t =>
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
          )
        )
          =
        (
          fun t =>
            spatial3.d
                zAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
              -
            spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component zAxis
                )
                x
        ) := by

      funext t
      rfl

    rw [hPointwise] at hSub

    simpa only [
      realVorticityY
    ] using hSub

  simpa only [
    logValue_mulVorticityY
  ] using hReal

/--
The z-vorticity logarithm is continuous in time when the logged first jet is
continuous.
-/
theorem vorticityZLogContinuousAt_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityZ u t x)
      )
      T := by

  have hReal :
      ContinuousAt
        (
          fun t =>
            realVorticityZ
              (PrimeTensor.Bridge.logSpaceTimeVectorField u)
              t x
        )
        T := by

    have hSub :=
      (hJet xAxis yAxis).sub
        (hJet yAxis xAxis)

    have hPointwise :
        (
          (
            fun t =>
              spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
          )
            -
          (
            fun t =>
              spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
          )
        )
          =
        (
          fun t =>
            spatial3.d
                xAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component yAxis
                )
                x
              -
            spatial3.d
                yAxis
                (
                  fun y =>
                    (
                      PrimeTensor.Bridge.logSpaceTimeVectorField
                        u t y
                    ).component xAxis
                )
                x
        ) := by

      funext t
      rfl

    rw [hPointwise] at hSub

    simpa only [
      realVorticityZ
    ] using hSub

  simpa only [
    logValue_mulVorticityZ
  ] using hReal

/--
Complete logged first-jet continuity implies the six primitive logarithmic
continuity conditions needed for any stretching component `j`.
-/
theorem stretchingPrimitiveLogContinuousAt_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    StretchingPrimitiveLogContinuousAt
      u T x j := by

  exact
    ⟨
      vorticityXLogContinuousAt_of_firstJet hJet,
      velocityGradientLogContinuousAt_of_firstJet
        hJet xAxis j,
      vorticityYLogContinuousAt_of_firstJet hJet,
      velocityGradientLogContinuousAt_of_firstJet
        hJet yAxis j,
      vorticityZLogContinuousAt_of_firstJet hJet,
      velocityGradientLogContinuousAt_of_firstJet
        hJet zAxis j
    ⟩

/--
A convergent time path plus logged first-jet continuity forces convergence of
all six primitive stretching inputs along the constant-field path.
-/
theorem stretchingPrimitivePathConvergent_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    StretchingPrimitivePathConvergent
      (constantVelocityRefinement u)
      u τ T x j := by

  exact
    stretchingPrimitivePathConvergent_of_timeContinuity
      hτ
      (
        stretchingPrimitiveLogContinuousAt_of_firstJet
          (j := j)
          hJet
      )

/--
Logged first-jet continuity rules out an explicit primitive cofinal leaf along
a convergent constant-field time path.
-/
theorem not_stretchingPrimitivePathCofinalFailure_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    {j : PrimeTensor.Axis Depth.three}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ StretchingPrimitivePathCofinalFailure
        (constantVelocityRefinement u)
        u τ T x j := by

  apply
    not_stretchingPrimitivePathCofinalFailure_of_convergent

  exact
    stretchingPrimitivePathConvergent_of_firstJet
      (j := j)
      hτ hJet

/--
X-component continuation criterion with the six primitive continuity hypotheses
replaced by one complete logged first-jet condition.
-/
theorem noCofinalVorticityBalancePathX_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (
            vorticityFieldPathX
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldX u T)
    )
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathX_of_timeContinuity
      hτ
      hStages
      hLimit
      hSecondJet
      (
        stretchingPrimitiveLogContinuousAt_of_firstJet
          (j := xAxis)
          hJet
      )

/-- Y-component continuation criterion from complete logged first-jet continuity. -/
theorem noCofinalVorticityBalancePathY_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (
            vorticityFieldPathY
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldY u T)
    )
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathY_of_timeContinuity
      hτ
      hStages
      hLimit
      hSecondJet
      (
        stretchingPrimitiveLogContinuousAt_of_firstJet
          (j := yAxis)
          hJet
      )

/-- Z-component continuation criterion from complete logged first-jet continuity. -/
theorem noCofinalVorticityBalancePathZ_of_firstJet
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    {x : Point3}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            u (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hSecondJet :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (
            vorticityFieldPathZ
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldZ u T)
    )
    (
      hJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  exact
    noCofinalVorticityBalancePathZ_of_timeContinuity
      hτ
      hStages
      hLimit
      hSecondJet
      (
        stretchingPrimitiveLogContinuousAt_of_firstJet
          (j := zAxis)
          hJet
      )

end Euclidean
end Bridge
end PrimeTensor
