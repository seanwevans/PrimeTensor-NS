import PrimeTensor.Fluid.Vorticity.Jet.Failure

/-!
# Analytic continuation handoff for the multiplicative vorticity cascade

The multiplicative argument is complete up to a classical continuation
estimate:

    cofinal unresolved balance
      -> terminal first-jet failure OR terminal third-jet failure.

A genuine Navier--Stokes continuation theorem needs two logically distinct
inputs:

1. an admissibility hypothesis saying that the field belongs to the relevant
   global incompressible Navier--Stokes solution class up to the candidate
   terminal time;
2. a preterminal analytic control, such as a Serrin-type norm or a vorticity
   maximum-norm time integral.

The previous version of this interface omitted the first item and therefore
made `closesJets` unrealistically strong: it asked a continuation estimate to
close the terminal jets of an arbitrary field.

This file corrects that boundary explicitly.

No PDE continuation theorem is assumed or proved here.  A concrete classical
criterion must provide both an `Admissible` predicate and a proof that
`Admissible + Holds` closes the terminal velocity-jet obstruction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
A classical continuation package for the logged velocity.

`Admissible u T` records that `u` belongs to the global solution class on the
preterminal interval needed by the analytic theorem.

`Holds u T` is the actual preterminal continuation control.

`closesJets` is the only substantive analytic implication required by the
multiplicative cascade.
-/
structure ContinuationControl where

  /--
  The solution-class hypothesis required by the classical continuation
  theorem.
  -/
  Admissible :
    PrimeTensor.SpaceTimeVectorField
        ℝ ℝ PrimeTensor.MulReal Depth.three →
      ℝ →
      Prop

  /-- The preterminal analytic condition. -/
  Holds :
    PrimeTensor.SpaceTimeVectorField
        ℝ ℝ PrimeTensor.MulReal Depth.three →
      ℝ →
      Prop

  /--
  A genuine continuation estimate:

  an admissible preterminal Navier--Stokes field satisfying the control cannot
  exhibit either terminal velocity-jet obstruction.
  -/
  closesJets :
    ∀
      (
        u :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three
      )
      (T : ℝ)
      (x : Point3),
      Admissible u T →
      Holds u T →
      VelocityLogSpatialC3 u →
      ¬ VelocityJetFailureAt u T x

namespace ContinuationControl

/--
Any continuation control is incompatible with a cofinally unresolved
X-vorticity balance along a convergent time path, provided the field lies in
the solution class required by the control.
-/
theorem not_holds_of_cofinalVorticityBalancePathX
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathX
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ C.Holds u T := by

  intro hControl

  have hJetFailure :
      VelocityJetFailureAt u T x :=
    velocityJetFailure_of_cofinalVorticityBalancePathX
      hτ
      hStages
      hLimit
      hSpatial
      hFailure

  exact
    (
      C.closesJets
        u T x
        hAdmissible
        hControl
        hSpatial
    )
    hJetFailure

/--
Any continuation control is incompatible with a cofinally unresolved
Y-vorticity balance along a convergent time path.
-/
theorem not_holds_of_cofinalVorticityBalancePathY
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathY
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ C.Holds u T := by

  intro hControl

  have hJetFailure :
      VelocityJetFailureAt u T x :=
    velocityJetFailure_of_cofinalVorticityBalancePathY
      hτ
      hStages
      hLimit
      hSpatial
      hFailure

  exact
    (
      C.closesJets
        u T x
        hAdmissible
        hControl
        hSpatial
    )
    hJetFailure

/--
Any continuation control is incompatible with a cofinally unresolved
Z-vorticity balance along a convergent time path.
-/
theorem not_holds_of_cofinalVorticityBalancePathZ
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathZ
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    ¬ C.Holds u T := by

  intro hControl

  have hJetFailure :
      VelocityJetFailureAt u T x :=
    velocityJetFailure_of_cofinalVorticityBalancePathZ
      hτ
      hStages
      hLimit
      hSpatial
      hFailure

  exact
    (
      C.closesJets
        u T x
        hAdmissible
        hControl
        hSpatial
    )
    hJetFailure

/--
If an admissible X-component field satisfies the continuation control, cofinal
unresolved balance is impossible.
-/
theorem noCofinalVorticityBalancePathX_of_holds
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hControl :
        C.Holds u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  exact
    (
      C.not_holds_of_cofinalVorticityBalancePathX
        hτ
        hStages
        hLimit
        hSpatial
        hAdmissible
        hFailure
    )
    hControl

/--
If an admissible Y-component field satisfies the continuation control, cofinal
unresolved balance is impossible.
-/
theorem noCofinalVorticityBalancePathY_of_holds
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hControl :
        C.Holds u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  exact
    (
      C.not_holds_of_cofinalVorticityBalancePathY
        hτ
        hStages
        hLimit
        hSpatial
        hAdmissible
        hFailure
    )
    hControl

/--
If an admissible Z-component field satisfies the continuation control, cofinal
unresolved balance is impossible.
-/
theorem noCofinalVorticityBalancePathZ_of_holds
    (C : ContinuationControl)
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
      hSpatial :
        VelocityLogSpatialC3 u
    )
    (
      hAdmissible :
        C.Admissible u T
    )
    (
      hControl :
        C.Holds u T
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  intro hFailure

  exact
    (
      C.not_holds_of_cofinalVorticityBalancePathZ
        hτ
        hStages
        hLimit
        hSpatial
        hAdmissible
        hFailure
    )
    hControl

end ContinuationControl

end Euclidean
end Bridge
end PrimeTensor
