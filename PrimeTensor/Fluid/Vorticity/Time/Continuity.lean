import PrimeTensor.Fluid.Vorticity.MovingTime.Leaves

/-!
# Time continuity as a continuation barrier for the moving-time cascade

The moving-time cascade ends in a fixed-scale cofinal failure of one primitive
stretching input.  For a single spacetime field `u`, approached along real
times `τ n -> T`, ordinary continuity of the six primitive logarithmic
coordinates at `T` forces all six native primitive paths to converge
intrinsically.

This file formalizes that implication.

The result is intentionally a continuation *criterion*, not yet a
Navier--Stokes continuation theorem.  In particular, the final balance
consequences still assume that a terminal field/time pair `(u,T)` exists and
satisfies the native vorticity balance, and they assume the corresponding
vorticity second-jet convergence needed to resolve diffusion.

What is proved here is the exact incompatibility:

    time-path convergence
    + primitive first-jet log continuity
    + diffusion second-jet convergence
    + balanced stage and terminal states

        => no cofinal unresolved balance cascade.

Thus any future blow-up argument must identify which one of those analytic
continuation properties cannot fail for smooth Navier--Stokes evolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- A constant refinement family carrying one spacetime velocity field. -/
noncomputable def constantVelocityRefinement
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    ) :
    VelocityRefinementSeq :=
  fun _ => u

/--
A positive-depth-indexed real time path converges to `T` along the native tail
filter.
-/
def TimePathConvergesTo
    (τ : TimeRefinementSeq)
    (T : ℝ) : Prop :=
  Filter.Tendsto
    τ
    PrimeTensor.Bridge.Depth.tailFilter
    (nhds T)

/--
Continuity at `T` of the six logarithmic primitive inputs to stretching
component `j`.
-/
def StretchingPrimitiveLogContinuousAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) : Prop :=
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityX u t x)
      )
      T
    ∧
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulSpatial3.d
                xAxis
                (fun y => (u t y).component j)
                x
            )
      )
      T
    ∧
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityY u t x)
      )
      T
    ∧
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulSpatial3.d
                yAxis
                (fun y => (u t y).component j)
                x
            )
      )
      T
    ∧
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (mulVorticityZ u t x)
      )
      T
    ∧
  ContinuousAt
      (
        fun t =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              mulSpatial3.d
                zAxis
                (fun y => (u t y).component j)
                x
            )
      )
      T

/--
A `MulReal`-valued time observable converges intrinsically along every
native-depth time path tending to `T` whenever its logarithmic coordinate is
continuous at `T`.
-/
theorem mulReal_timePath_converges_of_logContinuousAt
    {
      f : ℝ → PrimeTensor.MulReal
    }
    {
      τ : TimeRefinementSeq
    }
    {T : ℝ}
    (
      hτ :
        TimePathConvergesTo τ T
    )
    (
      hf :
        ContinuousAt
          (
            fun t =>
              PrimeTensor.Bridge.MulReal.logValue
                (f t)
          )
          T
    ) :
    PrimeTensor.MulReal.ConvergesTo
      (fun n => f (τ n))
      (f T) := by

  apply
    (
      PrimeTensor.Bridge.MulReal.convergesTo_iff_logValue_tendsto
        (fun n => f (τ n))
        (f T)
    ).2

  have hComp :=
    hf.tendsto.comp hτ

  simpa [Function.comp_def] using hComp

/--
Primitive log continuity at `T` forces convergence of all six primitive
moving-time channels for the constant-field path.
-/
theorem stretchingPrimitivePathConvergent_of_timeContinuity
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
      hContinuous :
        StretchingPrimitiveLogContinuousAt
          u T x j
    ) :
    StretchingPrimitivePathConvergent
      (constantVelocityRefinement u)
      u τ T x j := by

  rcases hContinuous with
    ⟨hωx, hDx, hωy, hDy, hωz, hDz⟩

  unfold StretchingPrimitivePathConvergent

  constructor

  · change
      PrimeTensor.MulReal.ConvergesTo
        (fun n => mulVorticityX u (τ n) x)
        (mulVorticityX u T x)

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (f := fun t => mulVorticityX u t x)
        hτ hωx

  constructor

  · change
      PrimeTensor.MulReal.ConvergesTo
        (
          fun n =>
            mulSpatial3.d
              xAxis
              (fun y => (u (τ n) y).component j)
              x
        )
        (
          mulSpatial3.d
            xAxis
            (fun y => (u T y).component j)
            x
        )

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (
          f :=
            fun t =>
              mulSpatial3.d
                xAxis
                (fun y => (u t y).component j)
                x
        )
        hτ hDx

  constructor

  · change
      PrimeTensor.MulReal.ConvergesTo
        (fun n => mulVorticityY u (τ n) x)
        (mulVorticityY u T x)

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (f := fun t => mulVorticityY u t x)
        hτ hωy

  constructor

  · change
      PrimeTensor.MulReal.ConvergesTo
        (
          fun n =>
            mulSpatial3.d
              yAxis
              (fun y => (u (τ n) y).component j)
              x
        )
        (
          mulSpatial3.d
            yAxis
            (fun y => (u T y).component j)
            x
        )

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (
          f :=
            fun t =>
              mulSpatial3.d
                yAxis
                (fun y => (u t y).component j)
                x
        )
        hτ hDy

  constructor

  · change
      PrimeTensor.MulReal.ConvergesTo
        (fun n => mulVorticityZ u (τ n) x)
        (mulVorticityZ u T x)

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (f := fun t => mulVorticityZ u t x)
        hτ hωz

  · change
      PrimeTensor.MulReal.ConvergesTo
        (
          fun n =>
            mulSpatial3.d
              zAxis
              (fun y => (u (τ n) y).component j)
              x
        )
        (
          mulSpatial3.d
            zAxis
            (fun y => (u T y).component j)
            x
        )

    exact
      mulReal_timePath_converges_of_logContinuousAt
        (
          f :=
            fun t =>
              mulSpatial3.d
                zAxis
                (fun y => (u t y).component j)
                x
        )
        hτ hDz

/--
Convergence of all six primitive channels rules out the explicit six-way
fixed-scale cofinal leaf.
-/
theorem not_stretchingPrimitivePathCofinalFailure_of_convergent
    {
      U : VelocityRefinementSeq
    }
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
      hConvergent :
        StretchingPrimitivePathConvergent
          U u τ T x j
    ) :
    ¬ StretchingPrimitivePathCofinalFailure
        U u τ T x j := by

  intro hFailure

  rcases hConvergent with
    ⟨hωx, hDx, hωy, hDy, hωz, hDz⟩

  unfold StretchingPrimitivePathCofinalFailure at hFailure

  rcases hFailure with
    hFailωx
      | hFailDx
      | hFailωy
      | hFailDy
      | hFailωz
      | hFailDz

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailωx
      ) hωx

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailDx
      ) hDx

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailωy
      ) hωy

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailDy
      ) hDy

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailωz
      ) hωz

  · exact
      (
        (
          PrimeTensor.MulReal.not_convergesTo_iff_exists_cofinalFailureAtScale
            _
            _
        ).2 hFailDz
      ) hDz

/--
Time continuity of the six primitive logs rules out a primitive cofinal leaf
along the constant-field time path.
-/
theorem not_stretchingPrimitivePathCofinalFailure_of_timeContinuity
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
      hContinuous :
        StretchingPrimitiveLogContinuousAt
          u T x j
    ) :
    ¬ StretchingPrimitivePathCofinalFailure
        (constantVelocityRefinement u)
        u τ T x j := by

  apply
    not_stretchingPrimitivePathCofinalFailure_of_convergent

  exact
    stretchingPrimitivePathConvergent_of_timeContinuity
      hτ hContinuous

/--
X-component continuation criterion.

For one spacetime field followed along a time path `τ -> T`, balanced stage and
terminal states, moving-time x-vorticity second-jet convergence, and primitive
log continuity exclude a cofinal unresolved x-balance cascade.
-/
theorem noCofinalVorticityBalancePathX_of_timeContinuity
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
      hContinuous :
        StretchingPrimitiveLogContinuousAt
          u T x xAxis
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hLeaf :=
    vorticityBalancePerturbationPathX_primitiveCofinalFailure
      (U := constantVelocityRefinement u)
      (u := u)
      (τ := τ)
      (T := T)
      (x := x)
      hStages
      hLimit
      hFailure
      hSecondJet

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_timeContinuity
        (u := u)
        (τ := τ)
        (T := T)
        (x := x)
        (j := xAxis)
        hτ
        hContinuous
    ) hLeaf

/-- Y-component continuation criterion. -/
theorem noCofinalVorticityBalancePathY_of_timeContinuity
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
      hContinuous :
        StretchingPrimitiveLogContinuousAt
          u T x yAxis
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hLeaf :=
    vorticityBalancePerturbationPathY_primitiveCofinalFailure
      (U := constantVelocityRefinement u)
      (u := u)
      (τ := τ)
      (T := T)
      (x := x)
      hStages
      hLimit
      hFailure
      hSecondJet

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_timeContinuity
        (u := u)
        (τ := τ)
        (T := T)
        (x := x)
        (j := yAxis)
        hτ
        hContinuous
    ) hLeaf

/-- Z-component continuation criterion. -/
theorem noCofinalVorticityBalancePathZ_of_timeContinuity
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
      hContinuous :
        StretchingPrimitiveLogContinuousAt
          u T x zAxis
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hLeaf :=
    vorticityBalancePerturbationPathZ_primitiveCofinalFailure
      (U := constantVelocityRefinement u)
      (u := u)
      (τ := τ)
      (T := T)
      (x := x)
      hStages
      hLimit
      hFailure
      hSecondJet

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_timeContinuity
        (u := u)
        (τ := τ)
        (T := T)
        (x := x)
        (j := zAxis)
        hτ
        hContinuous
    ) hLeaf

end Euclidean
end Bridge
end PrimeTensor
