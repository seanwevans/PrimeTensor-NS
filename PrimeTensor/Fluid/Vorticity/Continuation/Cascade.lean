import PrimeTensor.Fluid.Vorticity.Extension.Locality
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation

/-!
# Preterminal vorticity control excludes a continued multiplicative cascade

This file composes the two sides of the continuation architecture.

Analytic side:

    LoggedPreterminalNavierStokesAdmissible u T
      + VorticityL1LinfControl u T
      + VorticityL1LinfProducesExtension
      -> ∃ v, SmoothContinuationExtension u v T.

Classical-to-native bridge:

    LoggedPreterminalNavierStokesAdmissible u T
      + t ∈ (0,T)
      -> MulVorticityBalance3 u t x.

Hence every refinement time which remains strictly before `T` is automatically
a balanced native vorticity stage.

Multiplicative side:

    SmoothContinuationExtension u v T
      + TimePathConvergesTo τ T
      + TimePathStrictlyBefore τ T
      -> no cofinal X/Y/Z balance cascade for v.

The stagewise native balance hypothesis which appeared in the first version of
this module is therefore no longer an independent assumption.  The only major
analytic hypothesis deliberately left abstract here is
`VorticityL1LinfProducesExtension`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
All three native vorticity balances hold along a preterminal refinement path.
-/
def PreterminalVorticityBalancePath3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      τ : TimeRefinementSeq
    )
    (x : Point3) : Prop :=
  ∀ n : Depth,
    MulVorticityBalanceX u (τ n) x
      ∧
    MulVorticityBalanceY u (τ n) x
      ∧
    MulVorticityBalanceZ u (τ n) x

/--
Preterminal Navier--Stokes admissibility itself supplies the entire native
vorticity-balance path along any refinement which remains inside `(0,T)`.
-/
theorem preterminalVorticityBalancePath3_of_loggedPreterminalNavierStokes
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
      hAdmissible :
        LoggedPreterminalNavierStokesAdmissible
          u T
    )
    (
      hBefore :
        TimePathStrictlyBefore
          τ T
    ) :
    PreterminalVorticityBalancePath3
      u τ x := by

  intro n

  have hBalance :
      MulVorticityBalance3
        u (τ n) x :=
    mulVorticityBalance3_of_loggedPreterminalNavierStokes
      hAdmissible
      (hBefore n)

  exact hBalance

/--
All three componentwise cofinal cascades are absent for a continuation field
along the given terminal-time path.
-/
def NoCofinalVorticityCascade3
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      τ : TimeRefinementSeq
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  (
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathX
            (constantVelocityRefinement v)
            v τ T x
        )
  )
    ∧
  (
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathY
            (constantVelocityRefinement v)
            v τ T x
        )
  )
    ∧
  (
    ¬ MulBalanceState.CofinalFailureAtEveryScale
        (
          vorticityBalancePerturbationPathZ
            (constantVelocityRefinement v)
            v τ T x
        )
  )

/--
The composed continuation/cascade theorem with no independent stage-balance
hypothesis.

Assuming the genuine classical vorticity continuation theorem has been
formalized as `VorticityL1LinfProducesExtension`, an admissible preterminal
Navier--Stokes field satisfying the concrete vorticity `L¹_t L∞_x` control
admits a smooth continuation on which no componentwise cofinal multiplicative
vorticity cascade can persist along a time path approaching `T` strictly from
within the preterminal interval.

The X/Y/Z stage balances are derived internally from preterminal
Navier--Stokes admissibility.
-/
theorem vorticityL1LinfControl_produces_noCofinalCascade3
    (
      hContinuation :
        VorticityL1LinfProducesExtension
    )
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
      hAdmissible :
        LoggedPreterminalNavierStokesAdmissible
          u T
    )
    (
      hControl :
        VorticityL1LinfControl
          u T
    )
    (
      hτ :
        TimePathConvergesTo
          τ T
    )
    (
      hBefore :
        TimePathStrictlyBefore
          τ T
    ) :
    ∃
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three,
      SmoothContinuationExtension u v T
        ∧
      NoCofinalVorticityCascade3
        v τ T x := by

  obtain ⟨v, hExt⟩ :=
    hContinuation
      u T
      hAdmissible
      hControl

  have hStages :
      PreterminalVorticityBalancePath3
        u τ x :=
    preterminalVorticityBalancePath3_of_loggedPreterminalNavierStokes
      hAdmissible
      hBefore

  have hStagesX :
      ∀ n : Depth,
        MulVorticityBalanceX
          u (τ n) x := by
    intro n
    exact (hStages n).1

  have hStagesY :
      ∀ n : Depth,
        MulVorticityBalanceY
          u (τ n) x := by
    intro n
    exact (hStages n).2.1

  have hStagesZ :
      ∀ n : Depth,
        MulVorticityBalanceZ
          u (τ n) x := by
    intro n
    exact (hStages n).2.2

  refine ⟨v, hExt, ?_⟩

  unfold NoCofinalVorticityCascade3

  constructor

  · exact
      hExt.noCofinalVorticityBalancePathX
        hτ
        hBefore
        hStagesX

  · constructor

    · exact
        hExt.noCofinalVorticityBalancePathY
          hτ
          hBefore
          hStagesY

    · exact
        hExt.noCofinalVorticityBalancePathZ
          hτ
          hBefore
          hStagesZ

end Euclidean
end Bridge
end PrimeTensor
