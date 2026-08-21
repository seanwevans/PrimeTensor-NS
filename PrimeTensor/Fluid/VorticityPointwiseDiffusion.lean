import PrimeTensor.Fluid.VorticityFirstJetContinuity

/-!
# Pointwise diffusion control for moving-time vorticity balance

The earlier diffusion-refinement layer uses a field topology:

    FieldScale.SecondDerivativeConvergesTo D s f

which requires one eventual refinement anchor to control the same-axis second
derivatives at every spatial point simultaneously.

The moving-time cascade obstruction, however, is evaluated at one selected
point `x`.  Its diffusion slot only depends on the three same-axis second
derivatives of the corresponding vorticity component at that same point.

This file introduces the strictly local topology actually consumed by that
argument and rebuilds the diffusion-resolution / stretching-concentration chain
without any uniform-in-space assumption.

Scale accounting is explicit:

* three second-derivative factors form the multiplicative Laplacian: two levels;
* taking the oriented ratio to the terminal Laplacian: one further level.

Thus second-jet control at `succ (succ (succ level))` is sufficient to make the
relative diffusion slot near the pivot at `level`.
-/

namespace PrimeTensor

namespace FieldScale

/--
Same-axis second-derivative nearness at one selected spatial point.
-/
def SecondDerivativeNearAt
    {X : Type}
    {dim : Depth}
    (
      D :
        PrimeTensor.Differential
          X PrimeTensor.MulReal dim
    )
    (level : Depth)
    (f g : Field X dim)
    (x : PrimeTensor.Point X dim) : Prop :=
  ∀ i : PrimeTensor.Axis dim,
    MulReal.ScaleNear
      level
      (D.d i (D.d i f) x)
      (D.d i (D.d i g) x)

/--
A refinement family converges in the same-axis second jet at one selected
spatial point.
-/
def SecondDerivativeConvergesToAt
    {X : Type}
    {dim : Depth}
    (
      D :
        PrimeTensor.Differential
          X PrimeTensor.MulReal dim
    )
    (s : Seq X dim)
    (f : Field X dim)
    (x : PrimeTensor.Point X dim) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
          SecondDerivativeNearAt
            D level (s n) f x

/--
The earlier whole-field second-jet topology implies the new pointwise topology.
-/
theorem secondDerivativeConvergesToAt_of_global
    {X : Type}
    {dim : Depth}
    {
      D :
        PrimeTensor.Differential
          X PrimeTensor.MulReal dim
    }
    {s : Seq X dim}
    {f : Field X dim}
    {x : PrimeTensor.Point X dim}
    (
      h :
        SecondDerivativeConvergesTo
          D s f
    ) :
    SecondDerivativeConvergesToAt
      D s f x := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    h level

  refine ⟨anchor, ?_⟩

  intro n hn
  intro i

  exact
    hTail n hn i x

end FieldScale

namespace Bridge
namespace Euclidean

/--
Pointwise second-jet nearness two levels finer than `level` resolves the
three-factor multiplicative Laplacian at the selected point.
-/
theorem mulLaplacian3Field_nearAt
    {level : Depth}
    {
      f g :
        FieldScale.Field
          ℝ Depth.three
    }
    {x : Point3}
    (
      h :
        FieldScale.SecondDerivativeNearAt
          mulSpatial3
          (.succ (.succ level))
          f g x
    ) :
    MulReal.ScaleNear
      level
      (mulLaplacian3Field f x)
      (mulLaplacian3Field g x) := by

  have hxFine :=
    h xAxis

  have hyFine :=
    h yAxis

  have hzFine :=
    h zAxis

  have hx :
      MulReal.ScaleNear
        (.succ level)
        (
          mulSpatial3.d
            xAxis
            (mulSpatial3.d xAxis f)
            x
        )
        (
          mulSpatial3.d
            xAxis
            (mulSpatial3.d xAxis g)
            x
        ) :=
    MulReal.scaleNear_succ_weaken
      hxFine

  have hyz :
      MulReal.ScaleNear
        (.succ level)
        (
          mulSpatial3.d
              yAxis
              (mulSpatial3.d yAxis f)
              x
            *
          mulSpatial3.d
              zAxis
              (mulSpatial3.d zAxis f)
              x
        )
        (
          mulSpatial3.d
              yAxis
              (mulSpatial3.d yAxis g)
              x
            *
          mulSpatial3.d
              zAxis
              (mulSpatial3.d zAxis g)
              x
        ) :=
    MulReal.scaleNear_mul
      hyFine
      hzFine

  unfold mulLaplacian3Field

  exact
    MulReal.scaleNear_mul
      hx
      hyz

/--
Pointwise same-axis second-jet convergence implies scalar convergence of the
three-factor multiplicative Laplacian at the selected point.
-/
theorem mulLaplacian3Field_convergesAt
    {
      s :
        FieldScale.Seq
          ℝ Depth.three
    }
    {
      f :
        FieldScale.Field
          ℝ Depth.three
    }
    {x : Point3}
    (
      hs :
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          s f x
    ) :
    MulReal.ConvergesTo
      (fun n =>
        mulLaplacian3Field
          (s n) x)
      (mulLaplacian3Field f x) := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    hs (.succ (.succ level))

  refine ⟨anchor, ?_⟩

  intro n hn

  exact
    mulLaplacian3Field_nearAt
      (hTail n hn)

/--
Pointwise second-jet convergence makes the stagewise Laplacian ratio converge
to the multiplicative pivot.

The extra scale beyond `mulLaplacian3Field_convergesAt` is the cost of forming
the oriented ratio.
-/
theorem mulLaplacian3Field_ratio_convergesTo_one_at
    {
      s :
        FieldScale.Seq
          ℝ Depth.three
    }
    {
      f :
        FieldScale.Field
          ℝ Depth.three
    }
    {x : Point3}
    (
      hs :
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          s f x
    ) :
    MulReal.ConvergesTo
      (
        fun n =>
          MulReal.ratio
            (mulLaplacian3Field (s n) x)
            (mulLaplacian3Field f x)
      )
      (1 : MulReal) := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    hs (.succ (.succ (.succ level)))

  refine ⟨anchor, ?_⟩

  intro n hn

  have hLap :
      MulReal.ScaleNear
        (.succ level)
        (mulLaplacian3Field (s n) x)
        (mulLaplacian3Field f x) :=
    mulLaplacian3Field_nearAt
      (level := .succ level)
      (hTail n hn)

  exact
    MulReal.scaleNear_ratio_one
      hLap

/--
Pointwise x-vorticity second-jet convergence along a moving-time path is enough
to resolve the x-diffusion slot at the selected balance point.
-/
theorem vorticityBalancePerturbationPathX_diffusionConvergesAt
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
          x
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (
        vorticityBalancePerturbationPathX
          U u τ T x
      ) := by

  have hRatio :=
    mulLaplacian3Field_ratio_convergesTo_one_at
      hω

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathX,
    MulBalanceState.ratio,
    vorticityBalanceStateX,
    vorticityFieldPathX,
    mulVorticityDiffusionX_eq_mulLaplacian3Field
  ] using hRatio

/-- Pointwise moving-time y-diffusion resolution. -/
theorem vorticityBalancePerturbationPathY_diffusionConvergesAt
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
          x
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (
        vorticityBalancePerturbationPathY
          U u τ T x
      ) := by

  have hRatio :=
    mulLaplacian3Field_ratio_convergesTo_one_at
      hω

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathY,
    MulBalanceState.ratio,
    vorticityBalanceStateY,
    vorticityFieldPathY,
    mulVorticityDiffusionY_eq_mulLaplacian3Field
  ] using hRatio

/-- Pointwise moving-time z-diffusion resolution. -/
theorem vorticityBalancePerturbationPathZ_diffusionConvergesAt
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
          x
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (
        vorticityBalancePerturbationPathZ
          U u τ T x
      ) := by

  have hRatio :=
    mulLaplacian3Field_ratio_convergesTo_one_at
      hω

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationPathZ,
    MulBalanceState.ratio,
    vorticityBalanceStateZ,
    vorticityFieldPathZ,
    mulVorticityDiffusionZ_eq_mulLaplacian3Field
  ] using hRatio

/--
Moving-time x-vorticity concentration using only pointwise second-jet
convergence at the selected point.
-/
theorem vorticityBalancePerturbationPathX_cofinalStretchingAt
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
          (
            vorticityBalancePerturbationPathX
              U u τ T x
          )
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathX U τ)
          (vorticityFieldX u T)
          x
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (
        vorticityBalancePerturbationPathX
          U u τ T x
      ) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (
        vorticityBalancePerturbationPathX_balancedAll
          hStages hLimit
      )
      hFailure
      (
        vorticityBalancePerturbationPathX_diffusionConvergesAt
          hω
      )

/-- Moving-time y-vorticity concentration from pointwise second-jet convergence. -/
theorem vorticityBalancePerturbationPathY_cofinalStretchingAt
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
          (
            vorticityBalancePerturbationPathY
              U u τ T x
          )
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathY U τ)
          (vorticityFieldY u T)
          x
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (
        vorticityBalancePerturbationPathY
          U u τ T x
      ) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (
        vorticityBalancePerturbationPathY_balancedAll
          hStages hLimit
      )
      hFailure
      (
        vorticityBalancePerturbationPathY_diffusionConvergesAt
          hω
      )

/-- Moving-time z-vorticity concentration from pointwise second-jet convergence. -/
theorem vorticityBalancePerturbationPathZ_cofinalStretchingAt
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
          (
            vorticityBalancePerturbationPathZ
              U u τ T x
          )
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (vorticityFieldPathZ U τ)
          (vorticityFieldZ u T)
          x
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (
        vorticityBalancePerturbationPathZ
          U u τ T x
      ) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (
        vorticityBalancePerturbationPathZ_balancedAll
          hStages hLimit
      )
      hFailure
      (
        vorticityBalancePerturbationPathZ_diffusionConvergesAt
          hω
      )

/--
X-component continuation criterion using only pointwise diffusion second-jet
control plus complete logged first-jet time continuity.
-/
theorem noCofinalVorticityBalancePathX_of_pointwiseJets
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (
            vorticityFieldPathX
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldX u T)
          x
    )
    (
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hStretch :=
    vorticityBalancePerturbationPathX_cofinalStretchingAt
      hStages
      hLimit
      hFailure
      hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathX_cofinalStretchCouplingFailure
      hStretch

  have hPrimitive :=
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_firstJet
        (j := xAxis)
        hτ hFirstJet
    )
    hPrimitive

/-- Y-component pointwise-jet continuation criterion. -/
theorem noCofinalVorticityBalancePathY_of_pointwiseJets
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (
            vorticityFieldPathY
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldY u T)
          x
    )
    (
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hStretch :=
    vorticityBalancePerturbationPathY_cofinalStretchingAt
      hStages
      hLimit
      hFailure
      hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathY_cofinalStretchCouplingFailure
      hStretch

  have hPrimitive :=
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_firstJet
        (j := yAxis)
        hτ hFirstJet
    )
    hPrimitive

/-- Z-component pointwise-jet continuation criterion. -/
theorem noCofinalVorticityBalancePathZ_of_pointwiseJets
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
        FieldScale.SecondDerivativeConvergesToAt
          mulSpatial3
          (
            vorticityFieldPathZ
              (constantVelocityRefinement u)
              τ
          )
          (vorticityFieldZ u T)
          x
    )
    (
      hFirstJet :
        VelocityFirstJetLogContinuousAt
          u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  have hStretch :=
    vorticityBalancePerturbationPathZ_cofinalStretchingAt
      hStages
      hLimit
      hFailure
      hSecondJet

  have hCoupling :=
    vorticityBalancePerturbationPathZ_cofinalStretchCouplingFailure
      hStretch

  have hPrimitive :=
    stretchingPrimitivePathCofinalFailure_of_cofinalStretchCouplingFailure
      hCoupling

  exact
    (
      not_stretchingPrimitivePathCofinalFailure_of_firstJet
        (j := zAxis)
        hτ hFirstJet
    )
    hPrimitive

end Euclidean
end Bridge

end PrimeTensor
