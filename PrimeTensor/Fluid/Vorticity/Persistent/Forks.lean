import PrimeTensor.Fluid.Vorticity.Scale.Demand

/-!
# Persistent native vorticity scale forks

`VorticityScaleDemand` proves the one-step native fork:

    unresolved balance at `level`
      =>
    (temporal unresolved at `.succ level`
      OR transport unresolved at `.succ level`)
      AND
    (stretching unresolved at `.succ level`
      OR diffusion unresolved at `.succ level`).

The children of that fork are individual factors, not new four-term balance
states, so they must not yet be treated as recursively balanced nodes.

What *does* iterate immediately is the unresolved balance product itself.
Intrinsic nearness weakens from finer scales to coarser scales. Therefore,
by contraposition, failure of nearness at one scale persists at every finer
scale.

Combining persistent balance failure with the one-step fork theorem gives a
fork at every later intrinsic depth. This is the first honest persistent
cascade object: a failure spine through scale, emitting two factor forks at
each refinement level.

No norm, logarithm, subtraction, additive identity, ordinary metric, or
zeroth scale is introduced.
-/

namespace PrimeTensor
namespace MulBalanceState

def FailureAt
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  ¬ LeftNear q level

def ForkAt
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  LeftFactorFailure q level
    ∧
  RightFactorFailure q level

def PersistentFailureFrom
    (q : MulBalanceState)
    (base : Depth) : Prop :=
  ∀ level : Depth,
    Depth.AtOrAfter base level →
      FailureAt q level

def PersistentForksFrom
    (q : MulBalanceState)
    (base : Depth) : Prop :=
  ∀ level : Depth,
    Depth.AtOrAfter base level →
      ForkAt q level

theorem leftNear_weaken
    {q : MulBalanceState}
    {coarse fine : Depth}
    (hcf : Depth.AtOrAfter coarse fine)
    (hFine : LeftNear q fine) :
    LeftNear q coarse := by

  unfold LeftNear at hFine ⊢

  exact
    MulReal.scaleNear_weaken
      hcf
      hFine

theorem failureAt_of_atOrAfter
    {q : MulBalanceState}
    {base level : Depth}
    (hLevel : Depth.AtOrAfter base level)
    (hFailure : FailureAt q base) :
    FailureAt q level := by

  unfold FailureAt at hFailure ⊢

  intro hFine

  apply hFailure

  exact
    leftNear_weaken
      hLevel
      hFine

theorem persistentFailureFrom_of_failureAt
    {q : MulBalanceState}
    {base : Depth}
    (hFailure : FailureAt q base) :
    PersistentFailureFrom q base := by

  intro level hLevel

  exact
    failureAt_of_atOrAfter
      hLevel
      hFailure

theorem forkAt_of_balanced_failureAt
    {q : MulBalanceState}
    {level : Depth}
    (hBalance : Balanced q)
    (hFailure : FailureAt q level) :
    ForkAt q level := by

  unfold FailureAt at hFailure
  unfold ForkAt

  exact
    balancedFailure_forks
      hBalance
      hFailure

theorem persistentForksFrom_of_balanced_failureAt
    {q : MulBalanceState}
    {base : Depth}
    (hBalance : Balanced q)
    (hFailure : FailureAt q base) :
    PersistentForksFrom q base := by

  intro level hLevel

  have hFailureLevel :
      FailureAt q level :=
    failureAt_of_atOrAfter
      hLevel
      hFailure

  exact
    forkAt_of_balanced_failureAt
      hBalance
      hFailureLevel

theorem persistentFailure_and_forks
    {q : MulBalanceState}
    {base : Depth}
    (hBalance : Balanced q)
    (hFailure : FailureAt q base) :
    PersistentFailureFrom q base
      ∧
    PersistentForksFrom q base := by

  constructor

  · exact
      persistentFailureFrom_of_failureAt
        hFailure

  · exact
      persistentForksFrom_of_balanced_failureAt
        hBalance
        hFailure

end MulBalanceState

namespace Bridge
namespace Euclidean

theorem vorticityBalancePerturbationX_persistentForks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {base : Depth}
    (hu : MulVorticityBalanceX u t x)
    (hv : MulVorticityBalanceX v t x)
    (
      hFailure :
        MulBalanceState.FailureAt
          (vorticityBalancePerturbationX u v t x)
          base
    ) :
    MulBalanceState.PersistentForksFrom
      (vorticityBalancePerturbationX u v t x)
      base := by

  exact
    MulBalanceState.persistentForksFrom_of_balanced_failureAt
      (vorticityBalancePerturbationX_balanced hu hv)
      hFailure

theorem vorticityBalancePerturbationY_persistentForks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {base : Depth}
    (hu : MulVorticityBalanceY u t x)
    (hv : MulVorticityBalanceY v t x)
    (
      hFailure :
        MulBalanceState.FailureAt
          (vorticityBalancePerturbationY u v t x)
          base
    ) :
    MulBalanceState.PersistentForksFrom
      (vorticityBalancePerturbationY u v t x)
      base := by

  exact
    MulBalanceState.persistentForksFrom_of_balanced_failureAt
      (vorticityBalancePerturbationY_balanced hu hv)
      hFailure

theorem vorticityBalancePerturbationZ_persistentForks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {base : Depth}
    (hu : MulVorticityBalanceZ u t x)
    (hv : MulVorticityBalanceZ v t x)
    (
      hFailure :
        MulBalanceState.FailureAt
          (vorticityBalancePerturbationZ u v t x)
          base
    ) :
    MulBalanceState.PersistentForksFrom
      (vorticityBalancePerturbationZ u v t x)
      base := by

  exact
    MulBalanceState.persistentForksFrom_of_balanced_failureAt
      (vorticityBalancePerturbationZ_balanced hu hv)
      hFailure

end Euclidean
end Bridge
end PrimeTensor
