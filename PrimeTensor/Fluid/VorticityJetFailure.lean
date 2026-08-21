import PrimeTensor.Fluid.VorticityThirdJetContinuity

/-!
# Explicit velocity-jet failure forced by a persistent vorticity-balance cascade

`VorticityThirdJetContinuity` proves a continuation criterion in velocity-jet
language: if the logged velocity has time-continuous first and third spatial
jets at `(T,x)`, then the relative multiplicative vorticity balance cannot
remain unresolved cofinally along a time path approaching `T`.

This file records the contrapositive in the form needed for the next analytic
stage.

Under:

* `τ n -> T`,
* exact vorticity balance at every preterminal stage,
* exact balance at the terminal state,
* spatial `C³` regularity of every logged velocity component on every time
  slice,

a cofinally unresolved relative balance forces at least one of the following:

* failure of time continuity of the logged first spatial jet at `(T,x)`;
* failure of time continuity of the logged third spatial jet at `(T,x)`.

No new Navier--Stokes estimate is introduced here.  This theorem is the precise
handoff point to an external continuation estimate such as a Serrin- or
BKM-type criterion: that analytic estimate must rule out both jet failures from
preterminal control.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
The explicit terminal velocity-jet obstruction isolated by the multiplicative
cascade argument.
-/
def VelocityJetFailureAt
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  (¬ VelocityFirstJetLogContinuousAt u T x) ∨
  (¬ VelocityThirdJetLogContinuousAt u T x)

/--
X-component persistent balance failure forces failure of the logged first or
third velocity jet at the terminal point.
-/
theorem velocityJetFailure_of_cofinalVorticityBalancePathX
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
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathX
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    VelocityJetFailureAt u T x := by

  unfold VelocityJetFailureAt

  by_cases hFirst :
      VelocityFirstJetLogContinuousAt
        u T x

  · right

    intro hThird

    have hNoFailure :=
      noCofinalVorticityBalancePathX_of_velocityJets
        hτ
        hStages
        hLimit
        hSpatial
        ⟨hFirst, hThird⟩

    exact hNoFailure hFailure

  · exact Or.inl hFirst

/--
Y-component persistent balance failure forces failure of the logged first or
third velocity jet at the terminal point.
-/
theorem velocityJetFailure_of_cofinalVorticityBalancePathY
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
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathY
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    VelocityJetFailureAt u T x := by

  unfold VelocityJetFailureAt

  by_cases hFirst :
      VelocityFirstJetLogContinuousAt
        u T x

  · right

    intro hThird

    have hNoFailure :=
      noCofinalVorticityBalancePathY_of_velocityJets
        hτ
        hStages
        hLimit
        hSpatial
        ⟨hFirst, hThird⟩

    exact hNoFailure hFailure

  · exact Or.inl hFirst

/--
Z-component persistent balance failure forces failure of the logged first or
third velocity jet at the terminal point.
-/
theorem velocityJetFailure_of_cofinalVorticityBalancePathZ
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
      hFailure :
        MulBalanceState.CofinalFailureAtEveryScale
          (
            vorticityBalancePerturbationPathZ
              (constantVelocityRefinement u)
              u τ T x
          )
    ) :
    VelocityJetFailureAt u T x := by

  unfold VelocityJetFailureAt

  by_cases hFirst :
      VelocityFirstJetLogContinuousAt
        u T x

  · right

    intro hThird

    have hNoFailure :=
      noCofinalVorticityBalancePathZ_of_velocityJets
        hτ
        hStages
        hLimit
        hSpatial
        ⟨hFirst, hThird⟩

    exact hNoFailure hFailure

  · exact Or.inl hFirst

/--
Equivalent positive formulation: if neither terminal velocity-jet obstruction
occurs, then no X-component cofinal balance failure can occur.
-/
theorem noCofinalVorticityBalancePathX_of_noVelocityJetFailure
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
      hNoFailure :
        ¬ VelocityJetFailureAt u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  have hFirst :
      VelocityFirstJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inl h)

  have hThird :
      VelocityThirdJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inr h)

  exact
    noCofinalVorticityBalancePathX_of_velocityJets
      hτ
      hStages
      hLimit
      hSpatial
      ⟨hFirst, hThird⟩

/-- Y-component positive formulation. -/
theorem noCofinalVorticityBalancePathY_of_noVelocityJetFailure
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
      hNoFailure :
        ¬ VelocityJetFailureAt u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  have hFirst :
      VelocityFirstJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inl h)

  have hThird :
      VelocityThirdJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inr h)

  exact
    noCofinalVorticityBalancePathY_of_velocityJets
      hτ
      hStages
      hLimit
      hSpatial
      ⟨hFirst, hThird⟩

/-- Z-component positive formulation. -/
theorem noCofinalVorticityBalancePathZ_of_noVelocityJetFailure
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
      hNoFailure :
        ¬ VelocityJetFailureAt u T x
    ) :
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement u)
            u τ T x
        ) := by

  have hFirst :
      VelocityFirstJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inl h)

  have hThird :
      VelocityThirdJetLogContinuousAt u T x := by

    by_contra h

    exact hNoFailure (Or.inr h)

  exact
    noCofinalVorticityBalancePathZ_of_velocityJets
      hτ
      hStages
      hLimit
      hSpatial
      ⟨hFirst, hThird⟩

end Euclidean
end Bridge
end PrimeTensor
