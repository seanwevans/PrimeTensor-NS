import PrimeTensor.Fluid.Vorticity.Primitive.Leaves

/-!
# Moving-time refinement paths for native vorticity balance

The earlier refinement cascade compares a positive-depth family of spacetime
fields with a limiting field at one fixed evaluation time.  That is appropriate
for approximation families, but a finite-time singularity argument naturally
uses a stage-dependent time sequence

    tₙ -> T.

Freezing a time slice into a spacetime field is not acceptable: it changes the
temporal derivative and therefore need not preserve the Navier--Stokes balance.

This file introduces the correct moving-time refinement object.  Stage `n`
compares the vorticity balance state of `U n` at time `τ n` with the limiting
balance state of `u` at time `T`.

The abstract multiplicative balance machinery does not require the two balanced
states to have been evaluated at the same time.  Consequently the existing
cofinal concentration theorem applies unchanged once diffusion convergence is
proved along the moving-time field sequence.

This file stops at stretching concentration.  The next layer will generalize
the explicit stretching-coupling and primitive-leaf descent to the same
two-time comparison.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/-- Positive-depth-indexed real evaluation times. -/
abbrev TimeRefinementSeq :=
  Depth → ℝ

/-- Moving-time sequence of native x-vorticity fields. -/
noncomputable def vorticityFieldPathX
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq) :
    FieldScale.Seq ℝ Depth.three :=
  fun n =>
    vorticityFieldX
      (U n)
      (τ n)

/-- Moving-time sequence of native y-vorticity fields. -/
noncomputable def vorticityFieldPathY
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq) :
    FieldScale.Seq ℝ Depth.three :=
  fun n =>
    vorticityFieldY
      (U n)
      (τ n)

/-- Moving-time sequence of native z-vorticity fields. -/
noncomputable def vorticityFieldPathZ
    (U : VelocityRefinementSeq)
    (τ : TimeRefinementSeq) :
    FieldScale.Seq ℝ Depth.three :=
  fun n =>
    vorticityFieldZ
      (U n)
      (τ n)

/--
Moving-time relative x-vorticity balance state.

Stage `n` is evaluated at `τ n`; the limiting state is evaluated at `T`.
-/
noncomputable def vorticityBalancePerturbationPathX
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    MulBalanceState.ratio
      (vorticityBalanceStateX
        (U n) (τ n) x)
      (vorticityBalanceStateX
        u T x)

/-- Moving-time relative y-vorticity balance state. -/
noncomputable def vorticityBalancePerturbationPathY
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    MulBalanceState.ratio
      (vorticityBalanceStateY
        (U n) (τ n) x)
      (vorticityBalanceStateY
        u T x)

/-- Moving-time relative z-vorticity balance state. -/
noncomputable def vorticityBalancePerturbationPathZ
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (τ : TimeRefinementSeq)
    (T : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    MulBalanceState.ratio
      (vorticityBalanceStateZ
        (U n) (τ n) x)
      (vorticityBalanceStateZ
        u T x)

/-- Stagewise moving-time x-balances make the relative path balanced. -/
theorem vorticityBalancePerturbationPathX_balancedAll
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    ) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationPathX
        U u τ T x) := by

  intro n

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateX_balanced
        (hStages n))
      (vorticityBalanceStateX_balanced
        hLimit)

/-- Stagewise moving-time y-balances make the relative path balanced. -/
theorem vorticityBalancePerturbationPathY_balancedAll
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    ) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationPathY
        U u τ T x) := by

  intro n

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateY_balanced
        (hStages n))
      (vorticityBalanceStateY_balanced
        hLimit)

/-- Stagewise moving-time z-balances make the relative path balanced. -/
theorem vorticityBalancePerturbationPathZ_balancedAll
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    ) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationPathZ
        U u τ T x) := by

  intro n

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateZ_balanced
        (hStages n))
      (vorticityBalanceStateZ_balanced
        hLimit)

/--
Moving-time x-diffusion fields converge whenever the moving x-vorticity fields
converge in the same-axis second-jet topology.
-/
theorem mulVorticityDiffusionPathX_converges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionX
            (U n) (τ n) x
      )
      (
        fun x =>
          mulVorticityDiffusionX
            u T x
      ) := by

  simpa [
    vorticityFieldPathX,
    mulVorticityDiffusionX_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/-- Moving-time y-diffusion field convergence. -/
theorem mulVorticityDiffusionPathY_converges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionY
            (U n) (τ n) x
      )
      (
        fun x =>
          mulVorticityDiffusionY
            u T x
      ) := by

  simpa [
    vorticityFieldPathY,
    mulVorticityDiffusionY_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/-- Moving-time z-diffusion field convergence. -/
theorem mulVorticityDiffusionPathZ_converges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
    ) :
    FieldScale.ConvergesTo
      (
        fun n x =>
          mulVorticityDiffusionZ
            (U n) (τ n) x
      )
      (
        fun x =>
          mulVorticityDiffusionZ
            u T x
      ) := by

  simpa [
    vorticityFieldPathZ,
    mulVorticityDiffusionZ_eq_mulLaplacian3Field
  ] using
    (mulLaplacian3Field_converges hω)

/--
Second-jet convergence along a moving-time x-path makes the diffusion slot of
the relative x-balance path converge to the pivot.
-/
theorem vorticityBalancePerturbationPathX_diffusionConverges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationPathX
        U u τ T x) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n y =>
            mulVorticityDiffusionX
              (U n) (τ n) y
        )
        (
          fun y =>
            mulVorticityDiffusionX
              u T y
        ) :=
    mulVorticityDiffusionPathX_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  have hPoint :=
    FieldScale.convergesTo_at
      hRatio
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathX,
    MulBalanceState.ratio,
    vorticityBalanceStateX,
    FieldScale.ratioToLimit
  ] using hPoint

/-- Moving-time y-path diffusion-slot convergence. -/
theorem vorticityBalancePerturbationPathY_diffusionConverges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationPathY
        U u τ T x) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n y =>
            mulVorticityDiffusionY
              (U n) (τ n) y
        )
        (
          fun y =>
            mulVorticityDiffusionY
              u T y
        ) :=
    mulVorticityDiffusionPathY_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  have hPoint :=
    FieldScale.convergesTo_at
      hRatio
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathY,
    MulBalanceState.ratio,
    vorticityBalanceStateY,
    FieldScale.ratioToLimit
  ] using hPoint

/-- Moving-time z-path diffusion-slot convergence. -/
theorem vorticityBalancePerturbationPathZ_diffusionConverges
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
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationPathZ
        U u τ T x) := by

  have hDiffusion :
      FieldScale.ConvergesTo
        (
          fun n y =>
            mulVorticityDiffusionZ
              (U n) (τ n) y
        )
        (
          fun y =>
            mulVorticityDiffusionZ
              u T y
        ) :=
    mulVorticityDiffusionPathZ_converges
      hω

  have hRatio :=
    FieldScale.ratioToLimit_convergesTo_one
      hDiffusion

  have hPoint :=
    FieldScale.convergesTo_at
      hRatio
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathZ,
    MulBalanceState.ratio,
    vorticityBalanceStateZ,
    FieldScale.ratioToLimit
  ] using hPoint

/--
Moving-time x-vorticity concentration.
-/
theorem vorticityBalancePerturbationPathX_cofinalStretching
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceX
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceX
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathX
            U u τ T x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationPathX
        U u τ T x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationPathX_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationPathX_diffusionConverges
        hω)

/-- Moving-time y-vorticity concentration. -/
theorem vorticityBalancePerturbationPathY_cofinalStretching
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceY
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceY
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathY
            U u τ T x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationPathY
        U u τ T x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationPathY_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationPathY_diffusionConverges
        hω)

/-- Moving-time z-vorticity concentration. -/
theorem vorticityBalancePerturbationPathZ_cofinalStretching
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
    (
      hStages :
        ∀ n : Depth,
          MulVorticityBalanceZ
            (U n) (τ n) x
    )
    (
      hLimit :
        MulVorticityBalanceZ
          u T x
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationPathZ
            U u τ T x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationPathZ
        U u τ T x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationPathZ_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationPathZ_diffusionConverges
        hω)

end Euclidean
end Bridge
end PrimeTensor
