import PrimeTensor.Fluid.Vorticity.Persistent.Forks

/-!
# Diffusion resolution forces persistent stretching failure

The persistent native fork theorem gives, at every sufficiently fine scale,

    stretching failure OR diffusion failure.

At this point the project does *not* yet contain an intrinsic theorem proving
that the Euclidean second-derivative/Laplacian branch must eventually resolve.
The abstract `Differential` interface deliberately carries no such smoothing
axiom.

This file therefore isolates the exact missing analytic input:

    diffusion is resolved at every scale along the persistent failure spine.

Under precisely that hypothesis, the right-hand fork collapses to persistent
stretching failure.

This is a structural theorem, not yet a diffusion estimate.  It identifies the
next analytic obligation without introducing a norm, logarithm, subtraction,
additive identity, ordinary metric, or zeroth scale.
-/

namespace PrimeTensor
namespace MulBalanceState

/--
The diffusion factor is resolved at the one-finer scale required by the
balance product at `level`.
-/
def DiffusionResolvedAt
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  MulReal.ScaleNear
    (.succ level)
    q.diffusion
    1

/--
The stretching factor remains unresolved at the one-finer scale required by
the balance product at `level`.
-/
def StretchingFailureAt
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  ¬ MulReal.ScaleNear
      (.succ level)
      q.stretching
      1

/--
Diffusion is resolved along every scale in the tail beginning at `base`.

This is intentionally a hypothesis interface.  A later analytic theorem must
derive it from genuine properties of the native Euclidean diffusion operator.
-/
def DiffusionResolvedFrom
    (q : MulBalanceState)
    (base : Depth) : Prop :=
  ∀ level : Depth,
    Depth.AtOrAfter base level →
      DiffusionResolvedAt q level

/--
Stretching remains unresolved along every scale in the tail beginning at
`base`.
-/
def PersistentStretchingFailureFrom
    (q : MulBalanceState)
    (base : Depth) : Prop :=
  ∀ level : Depth,
    Depth.AtOrAfter base level →
      StretchingFailureAt q level

/--
At one scale, if the right-hand fork fails in at least one child and diffusion
is resolved, then the unresolved child must be stretching.
-/
theorem stretchingFailure_of_rightFactorFailure_of_diffusionResolved
    {q : MulBalanceState}
    {level : Depth}
    (hFork : RightFactorFailure q level)
    (hDiffusion : DiffusionResolvedAt q level) :
    StretchingFailureAt q level := by

  unfold RightFactorFailure at hFork
  unfold DiffusionResolvedAt at hDiffusion
  unfold StretchingFailureAt

  rcases hFork with hStretching | hDiffusionFailure

  · exact hStretching

  · exact False.elim (hDiffusionFailure hDiffusion)

/--
Persistent right-hand forks plus persistent diffusion resolution force
persistent stretching failure.
-/
theorem persistentStretchingFailureFrom_of_forks_of_diffusionResolved
    {q : MulBalanceState}
    {base : Depth}
    (hForks : PersistentForksFrom q base)
    (hDiffusion : DiffusionResolvedFrom q base) :
    PersistentStretchingFailureFrom q base := by

  intro level hLevel

  have hFork :
      ForkAt q level :=
    hForks level hLevel

  have hDiffusionLevel :
      DiffusionResolvedAt q level :=
    hDiffusion level hLevel

  exact
    stretchingFailure_of_rightFactorFailure_of_diffusionResolved
      hFork.2
      hDiffusionLevel

/--
A balanced unresolved perturbation whose diffusion branch resolves throughout
the tail must carry all persistent right-side scale demand in stretching.
-/
theorem persistentStretchingFailureFrom_of_balanced_failure_diffusionResolved
    {q : MulBalanceState}
    {base : Depth}
    (hBalance : Balanced q)
    (hFailure : FailureAt q base)
    (hDiffusion : DiffusionResolvedFrom q base) :
    PersistentStretchingFailureFrom q base := by

  have hForks :
      PersistentForksFrom q base :=
    persistentForksFrom_of_balanced_failureAt
      hBalance
      hFailure

  exact
    persistentStretchingFailureFrom_of_forks_of_diffusionResolved
      hForks
      hDiffusion

end MulBalanceState

namespace Bridge
namespace Euclidean

/--
For the relative x-vorticity state of two native balanced fields, persistent
diffusion resolution forces persistent stretching failure.
-/
theorem vorticityBalancePerturbationX_diffusionResolution_forces_stretching
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
    )
    (
      hDiffusion :
        MulBalanceState.DiffusionResolvedFrom
          (vorticityBalancePerturbationX u v t x)
          base
    ) :
    MulBalanceState.PersistentStretchingFailureFrom
      (vorticityBalancePerturbationX u v t x)
      base := by

  exact
    PrimeTensor.MulBalanceState.persistentStretchingFailureFrom_of_balanced_failure_diffusionResolved
        (vorticityBalancePerturbationX_balanced hu hv)
        hFailure
        hDiffusion

/--
For the relative y-vorticity state of two native balanced fields, persistent
diffusion resolution forces persistent stretching failure.
-/
theorem vorticityBalancePerturbationY_diffusionResolution_forces_stretching
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
    )
    (
      hDiffusion :
        MulBalanceState.DiffusionResolvedFrom
          (vorticityBalancePerturbationY u v t x)
          base
    ) :
    MulBalanceState.PersistentStretchingFailureFrom
      (vorticityBalancePerturbationY u v t x)
      base := by

  exact
    PrimeTensor.MulBalanceState.persistentStretchingFailureFrom_of_balanced_failure_diffusionResolved
        (vorticityBalancePerturbationY_balanced hu hv)
        hFailure
        hDiffusion

/--
For the relative z-vorticity state of two native balanced fields, persistent
diffusion resolution forces persistent stretching failure.
-/
theorem vorticityBalancePerturbationZ_diffusionResolution_forces_stretching
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
    )
    (
      hDiffusion :
        MulBalanceState.DiffusionResolvedFrom
          (vorticityBalancePerturbationZ u v t x)
          base
    ) :
    MulBalanceState.PersistentStretchingFailureFrom
      (vorticityBalancePerturbationZ u v t x)
      base := by

  exact
    PrimeTensor.MulBalanceState.persistentStretchingFailureFrom_of_balanced_failure_diffusionResolved
        (vorticityBalancePerturbationZ_balanced hu hv)
        hFailure
        hDiffusion

end Euclidean
end Bridge
end PrimeTensor
