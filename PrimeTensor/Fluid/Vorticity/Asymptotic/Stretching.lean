import PrimeTensor.Fluid.Vorticity.Refinement.Diffusion

/-!
# Asymptotic concentration of unresolved vorticity demand into stretching

The refinement-indexed diffusion theorem gives ordinary intrinsic convergence:

    for every fixed output scale,
    sufficiently late refinement stages resolve the diffusion ratio.

That does **not** imply a uniform diagonal estimate for an arbitrarily
fast-growing scale schedule.  No such rate is assumed here.

Instead we formulate the exact cofinal statement needed for a singular
refinement cascade.

A sequence of multiplicative balance states has cofinal failure at every scale
when, for every requested intrinsic scale and every refinement-stage anchor,
there is a later stage whose balance product is still unresolved at that scale.

If

* every stage is balanced,
* unresolved balance demand occurs cofinally at every scale, and
* the diffusion slot converges to the multiplicative pivot,

then stretching failure also occurs cofinally at every scale.

The proof is purely intrinsic.  At a requested scale, first move beyond the
diffusion-convergence anchor.  Cofinal balance failure supplies an even later
unresolved balanced stage.  At that same stage diffusion is resolved, so the
right-hand fork can only be carried by stretching.

No norm, subtraction, additive identity, ordinary metric, logarithm, uniform
convergence rate, or zeroth scale is introduced.
-/

namespace PrimeTensor

namespace FieldScale

/--
Pointwise evaluation of a convergent field refinement family is a convergent
`MulReal` refinement sequence.
-/
theorem convergesTo_at
    {X : Type}
    {dim : Depth}
    {s : Seq X dim}
    {f : Field X dim}
    (hs : ConvergesTo s f)
    (x : PrimeTensor.Point X dim) :
    MulReal.ConvergesTo
      (fun n => s n x)
      (f x) := by

  intro level

  obtain ⟨anchor, hTail⟩ :=
    hs level

  refine ⟨anchor, ?_⟩

  intro n hn

  exact
    hTail n hn x

end FieldScale

namespace MulBalanceState

/-- A positive-depth-indexed refinement family of multiplicative balance states. -/
abbrev RefinementSeq :=
  Depth → MulBalanceState

/-- Every stage of a balance refinement family satisfies the native balance. -/
def BalancedAll
    (q : RefinementSeq) : Prop :=
  ∀ n : Depth,
    Balanced (q n)

/--
Unresolved balance demand occurs arbitrarily late at every intrinsic scale.

The scale and the refinement-stage anchor are independent quantifiers.  This
is deliberately weaker and more honest than assuming a uniform diagonal rate.
-/
def CofinalFailureAtEveryScale
    (q : RefinementSeq) : Prop :=
  ∀ level anchor : Depth,
    ∃ n : Depth,
      Depth.AtOrAfter anchor n
        ∧
      FailureAt (q n) level

/--
The diffusion slot of a balance refinement family converges to the
multiplicative pivot.
-/
def DiffusionConvergesToPivot
    (q : RefinementSeq) : Prop :=
  MulReal.ConvergesTo
    (fun n =>
      (q n).diffusion)
    1

/--
Stretching failure occurs arbitrarily late at every intrinsic scale.
-/
def CofinalStretchingFailureAtEveryScale
    (q : RefinementSeq) : Prop :=
  ∀ level anchor : Depth,
    ∃ n : Depth,
      Depth.AtOrAfter anchor n
        ∧
      StretchingFailureAt
        (q n)
        level

/--
Cofinal unresolved balance demand plus convergent diffusion forces cofinal
stretching failure.

For a requested `level` and arbitrary stage `anchor`:

1. diffusion convergence gives a later anchor where the diffusion factor is
   resolved at `.succ level`;
2. cofinal balance failure gives a still later unresolved stage;
3. balance creates the right-hand fork;
4. the resolved diffusion child leaves stretching as the only possible failed
   child.
-/
theorem cofinalStretchingFailure_of_balanced_failure_diffusion
    {q : RefinementSeq}
    (hBalanced : BalancedAll q)
    (hFailure : CofinalFailureAtEveryScale q)
    (hDiffusion : DiffusionConvergesToPivot q) :
    CofinalStretchingFailureAtEveryScale q := by

  intro level anchor

  obtain ⟨diffusionAnchor, hDiffusionTail⟩ :=
    hDiffusion (.succ level)

  let commonAnchor :=
    Depth.join anchor diffusionAnchor

  obtain ⟨n, hnCommon, hFailureN⟩ :=
    hFailure level commonAnchor

  have hnAnchor :
      Depth.AtOrAfter anchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.left_atOrAfter anchor diffusionAnchor)
        hnCommon

  have hnDiffusionAnchor :
      Depth.AtOrAfter diffusionAnchor n := by

    exact
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter anchor diffusionAnchor)
        hnCommon

  have hDiffusionN :
      DiffusionResolvedAt
        (q n)
        level := by

    unfold DiffusionResolvedAt

    exact
      hDiffusionTail
        n
        hnDiffusionAnchor

  have hForkN :
      RightFactorFailure
        (q n)
        level := by

    exact
      (
        balancedFailure_forks
          (hBalanced n)
          hFailureN
      ).2

  have hStretchingN :
      StretchingFailureAt
        (q n)
        level :=
    stretchingFailure_of_rightFactorFailure_of_diffusionResolved
      hForkN
      hDiffusionN

  exact
    ⟨n, hnAnchor, hStretchingN⟩

end MulBalanceState

namespace Bridge
namespace Euclidean

/-- Refinement family of relative x-vorticity balance states at fixed `t,x`. -/
noncomputable def vorticityBalancePerturbationSeqX
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    vorticityBalancePerturbationX
      (U n) u t x

/-- Refinement family of relative y-vorticity balance states at fixed `t,x`. -/
noncomputable def vorticityBalancePerturbationSeqY
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    vorticityBalancePerturbationY
      (U n) u t x

/-- Refinement family of relative z-vorticity balance states at fixed `t,x`. -/
noncomputable def vorticityBalancePerturbationSeqZ
    (U : VelocityRefinementSeq)
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState.RefinementSeq :=
  fun n =>
    vorticityBalancePerturbationZ
      (U n) u t x

/--
Stagewise x-balance hypotheses make the entire relative x-vorticity refinement
family balanced.
-/
theorem vorticityBalancePerturbationSeqX_balancedAll
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceX
          (U n) t x)
    (hLimit :
      MulVorticityBalanceX
        u t x) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationSeqX
        U u t x) := by

  intro n

  exact
    vorticityBalancePerturbationX_balanced
      (hStages n)
      hLimit

/--
Stagewise y-balance hypotheses make the entire relative y-vorticity refinement
family balanced.
-/
theorem vorticityBalancePerturbationSeqY_balancedAll
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceY
          (U n) t x)
    (hLimit :
      MulVorticityBalanceY
        u t x) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationSeqY
        U u t x) := by

  intro n

  exact
    vorticityBalancePerturbationY_balanced
      (hStages n)
      hLimit

/--
Stagewise z-balance hypotheses make the entire relative z-vorticity refinement
family balanced.
-/
theorem vorticityBalancePerturbationSeqZ_balancedAll
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceZ
          (U n) t x)
    (hLimit :
      MulVorticityBalanceZ
        u t x) :
    MulBalanceState.BalancedAll
      (vorticityBalancePerturbationSeqZ
        U u t x) := by

  intro n

  exact
    vorticityBalancePerturbationZ_balanced
      (hStages n)
      hLimit

/--
Second-jet convergence of x-vorticity gives convergence of the actual diffusion
slot of the relative x-balance sequence.
-/
theorem vorticityBalancePerturbationSeqX_diffusionConverges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqX U t)
          (vorticityFieldX u t)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationSeqX
        U u t x) := by

  have hField :=
    vorticityBalancePerturbationX_diffusion_convergesTo_one
      hω

  have hPoint :=
    FieldScale.convergesTo_at
      hField
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationSeqX
  ] using hPoint

/--
Second-jet convergence of y-vorticity gives convergence of the actual diffusion
slot of the relative y-balance sequence.
-/
theorem vorticityBalancePerturbationSeqY_diffusionConverges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqY U t)
          (vorticityFieldY u t)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationSeqY
        U u t x) := by

  have hField :=
    vorticityBalancePerturbationY_diffusion_convergesTo_one
      hω

  have hPoint :=
    FieldScale.convergesTo_at
      hField
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationSeqY
  ] using hPoint

/--
Second-jet convergence of z-vorticity gives convergence of the actual diffusion
slot of the relative z-balance sequence.
-/
theorem vorticityBalancePerturbationSeqZ_diffusionConverges
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqZ U t)
          (vorticityFieldZ u t)
    ) :
    MulBalanceState.DiffusionConvergesToPivot
      (vorticityBalancePerturbationSeqZ
        U u t x) := by

  have hField :=
    vorticityBalancePerturbationZ_diffusion_convergesTo_one
      hω

  have hPoint :=
    FieldScale.convergesTo_at
      hField
      x

  simpa [
    MulBalanceState.DiffusionConvergesToPivot,
    vorticityBalancePerturbationSeqZ
  ] using hPoint

/--
Asymptotic x-vorticity concentration theorem.

If balanced relative x-vorticity approximants remain unresolved arbitrarily
late at every scale, while the x-vorticity second jet converges, then
stretching failure occurs arbitrarily late at every scale.
-/
theorem vorticityBalancePerturbationSeqX_cofinalStretching
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceX
          (U n) t x)
    (hLimit :
      MulVorticityBalanceX
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqX
            U u t x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqX U t)
          (vorticityFieldX u t)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationSeqX
        U u t x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationSeqX_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationSeqX_diffusionConverges
        hω)

/--
Asymptotic y-vorticity concentration theorem.
-/
theorem vorticityBalancePerturbationSeqY_cofinalStretching
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceY
          (U n) t x)
    (hLimit :
      MulVorticityBalanceY
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqY
            U u t x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqY U t)
          (vorticityFieldY u t)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationSeqY
        U u t x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationSeqY_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationSeqY_diffusionConverges
        hω)

/--
Asymptotic z-vorticity concentration theorem.
-/
theorem vorticityBalancePerturbationSeqZ_cofinalStretching
    {
      U : VelocityRefinementSeq
    }
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hStages :
      ∀ n : Depth,
        MulVorticityBalanceZ
          (U n) t x)
    (hLimit :
      MulVorticityBalanceZ
        u t x)
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (vorticityBalancePerturbationSeqZ
            U u t x)
    )
    (
      hω :
        FieldScale.SecondDerivativeConvergesTo
          mulSpatial3
          (vorticityFieldSeqZ U t)
          (vorticityFieldZ u t)
    ) :
    MulBalanceState.CofinalStretchingFailureAtEveryScale
      (vorticityBalancePerturbationSeqZ
        U u t x) := by

  exact
    MulBalanceState.cofinalStretchingFailure_of_balanced_failure_diffusion
      (vorticityBalancePerturbationSeqZ_balancedAll
        hStages hLimit)
      hFailure
      (vorticityBalancePerturbationSeqZ_diffusionConverges
        hω)

end Euclidean
end Bridge
end PrimeTensor
