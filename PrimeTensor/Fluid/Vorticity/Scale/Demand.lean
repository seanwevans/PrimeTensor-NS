import PrimeTensor.Bridge.Euclidean.Vorticity.Native
import PrimeTensor.Analysis.Rules

/-!
# Native scale-demand forks for multiplicative vorticity balance

The native vorticity equation has the componentwise form

    temporal * transport = stretching * diffusion.

To study scale demand we must not confuse amplitude with refinement.  A raw
state need not be near the multiplicative pivot `1`.  Perturbations, however,
are intrinsically represented by oriented ratios, exactly as in the native
multiplicative derivative.

This file therefore compares two balanced states componentwise.  Their four
oriented ratios form a new multiplicative balance.  Since multiplication costs
one intrinsic refinement level, failure of either product ratio to be near the
pivot at `level` forces failure of at least one child ratio at `.succ level`.

For a balanced perturbation this happens on both sides simultaneously:

    unresolved (temporal * transport)
        => unresolved temporal OR unresolved transport

and, by balance,

    unresolved (stretching * diffusion)
        => unresolved stretching OR unresolved diffusion.

This is the first native branching/cascade statement.  It introduces no norm,
subtraction, additive identity, logarithm, or zeroth scale.
-/

namespace PrimeTensor

/--
A four-term multiplicative balance state.

The intended interpretation for vorticity is

* `temporal`   = temporal response,
* `transport`  = nonlinear transport,
* `stretching` = vortex stretching,
* `diffusion`  = diffusion.
-/
structure MulBalanceState where
  temporal : MulReal
  transport : MulReal
  stretching : MulReal
  diffusion : MulReal

namespace MulBalanceState

/-- Native four-term balance law. -/
def Balanced (q : MulBalanceState) : Prop :=
  q.temporal * q.transport =
    q.stretching * q.diffusion

/--
Componentwise oriented ratio between two balance states.

This is the correct object for scale analysis: every field is a relative
perturbation and is therefore naturally compared with the pivot `1`.
-/
noncomputable def ratio
    (a b : MulBalanceState) :
    MulBalanceState where
  temporal :=
    MulReal.ratio a.temporal b.temporal
  transport :=
    MulReal.ratio a.transport b.transport
  stretching :=
    MulReal.ratio a.stretching b.stretching
  diffusion :=
    MulReal.ratio a.diffusion b.diffusion

/--
The ratio of two balanced states is itself balanced.

This is the multiplicative analogue of subtracting two additive equations,
but it uses only oriented ratios and multiplication.
-/
theorem ratio_balanced
    {a b : MulBalanceState}
    (ha : Balanced a)
    (hb : Balanced b) :
    Balanced (ratio a b) := by

  unfold Balanced at ha hb ⊢
  unfold ratio

  calc
    MulReal.ratio a.temporal b.temporal *
          MulReal.ratio a.transport b.transport
        =
      MulReal.ratio
        (a.temporal * a.transport)
        (b.temporal * b.transport) :=
          (MulReal.ratio_mul_pair
            a.temporal b.temporal
            a.transport b.transport).symm

    _ =
      MulReal.ratio
        (a.stretching * a.diffusion)
        (b.stretching * b.diffusion) := by
          rw [ha, hb]

    _ =
      MulReal.ratio a.stretching b.stretching *
        MulReal.ratio a.diffusion b.diffusion :=
          MulReal.ratio_mul_pair
            a.stretching b.stretching
            a.diffusion b.diffusion

/--
The temporal/transport product perturbation is resolved at `level`.
-/
def LeftNear
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  MulReal.ScaleNear
    level
    (q.temporal * q.transport)
    1

/--
The stretching/diffusion product perturbation is resolved at `level`.
-/
def RightNear
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  MulReal.ScaleNear
    level
    (q.stretching * q.diffusion)
    1

/--
At the input scale required by multiplication, both temporal-side factors are
resolved.
-/
def LeftFactorsNear
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  MulReal.ScaleNear
      (.succ level)
      q.temporal
      1
    ∧
  MulReal.ScaleNear
      (.succ level)
      q.transport
      1

/--
At the input scale required by multiplication, both stretching-side factors
are resolved.
-/
def RightFactorsNear
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  MulReal.ScaleNear
      (.succ level)
      q.stretching
      1
    ∧
  MulReal.ScaleNear
      (.succ level)
      q.diffusion
      1

/--
Failure of the temporal/transport side at `level` must occur in at least one
factor at the one-finer input scale.
-/
def LeftFactorFailure
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  (¬ MulReal.ScaleNear
      (.succ level)
      q.temporal
      1)
    ∨
  (¬ MulReal.ScaleNear
      (.succ level)
      q.transport
      1)

/--
Failure of the stretching/diffusion side at `level` must occur in at least one
factor at the one-finer input scale.
-/
def RightFactorFailure
    (q : MulBalanceState)
    (level : Depth) : Prop :=
  (¬ MulReal.ScaleNear
      (.succ level)
      q.stretching
      1)
    ∨
  (¬ MulReal.ScaleNear
      (.succ level)
      q.diffusion
      1)

/--
One additional level of refinement in each temporal-side factor resolves their
product at the requested level.
-/
theorem leftNear_of_factorsNear
    {q : MulBalanceState}
    {level : Depth}
    (h : LeftFactorsNear q level) :
    LeftNear q level := by

  rcases h with ⟨hTemporal, hTransport⟩

  unfold LeftNear

  simpa using
    (MulReal.scaleNear_mul
      hTemporal
      hTransport)

/--
One additional level of refinement in each stretching-side factor resolves
their product at the requested level.
-/
theorem rightNear_of_factorsNear
    {q : MulBalanceState}
    {level : Depth}
    (h : RightFactorsNear q level) :
    RightNear q level := by

  rcases h with ⟨hStretching, hDiffusion⟩

  unfold RightNear

  simpa using
    (MulReal.scaleNear_mul
      hStretching
      hDiffusion)

/--
Contrapositive localization of the multiplication cost on the
temporal/transport side.
-/
theorem leftFactorFailure_of_leftFailure
    {q : MulBalanceState}
    {level : Depth}
    (hFailure : ¬ LeftNear q level) :
    LeftFactorFailure q level := by

  classical

  unfold LeftFactorFailure

  by_cases hTemporal :
      MulReal.ScaleNear
        (.succ level)
        q.temporal
        1

  · right
    intro hTransport

    apply hFailure
    apply leftNear_of_factorsNear

    exact ⟨hTemporal, hTransport⟩

  · exact Or.inl hTemporal

/--
Contrapositive localization of the multiplication cost on the
stretching/diffusion side.
-/
theorem rightFactorFailure_of_rightFailure
    {q : MulBalanceState}
    {level : Depth}
    (hFailure : ¬ RightNear q level) :
    RightFactorFailure q level := by

  classical

  unfold RightFactorFailure

  by_cases hStretching :
      MulReal.ScaleNear
        (.succ level)
        q.stretching
        1

  · right
    intro hDiffusion

    apply hFailure
    apply rightNear_of_factorsNear

    exact ⟨hStretching, hDiffusion⟩

  · exact Or.inl hStretching

/--
For a balanced perturbation, resolution of the left product and right product
is the same statement.
-/
theorem leftNear_iff_rightNear
    {q : MulBalanceState}
    {level : Depth}
    (hBalance : Balanced q) :
    LeftNear q level ↔
      RightNear q level := by

  unfold Balanced at hBalance
  unfold LeftNear RightNear

  rw [hBalance]

/--
For a balanced perturbation, failure of the temporal/transport product is also
failure of the stretching/diffusion product.
-/
theorem rightFailure_of_leftFailure
    {q : MulBalanceState}
    {level : Depth}
    (hBalance : Balanced q)
    (hFailure : ¬ LeftNear q level) :
    ¬ RightNear q level := by

  intro hRight

  apply hFailure

  exact
    (leftNear_iff_rightNear hBalance).mpr
      hRight

/--
The native two-sided refinement fork.

If a balanced perturbation cannot be resolved at `level`, then one refinement
level deeper:

* temporal or transport still fails, and
* stretching or diffusion still fails.

Thus unresolved scale demand cannot disappear at the balance node.  It must
continue into at least one child on each side.
-/
theorem balancedFailure_forks
    {q : MulBalanceState}
    {level : Depth}
    (hBalance : Balanced q)
    (hFailure : ¬ LeftNear q level) :
    LeftFactorFailure q level
      ∧
    RightFactorFailure q level := by

  constructor

  · exact
      leftFactorFailure_of_leftFailure
        hFailure

  · exact
      rightFactorFailure_of_rightFailure
        (rightFailure_of_leftFailure
          hBalance
          hFailure)

end MulBalanceState

namespace Bridge
namespace Euclidean

/--
Package the native x-vorticity component as a four-term balance state.
-/
noncomputable def vorticityBalanceStateX
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState where

  temporal :=
    mulTemporalVorticityX u t x

  transport :=
    mulVorticityTransportX u t x

  stretching :=
    mulVortexStretchComponent
      u t x xAxis

  diffusion :=
    mulVorticityDiffusionX u t x

/--
Package the native y-vorticity component as a four-term balance state.
-/
noncomputable def vorticityBalanceStateY
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState where

  temporal :=
    mulTemporalVorticityY u t x

  transport :=
    mulVorticityTransportY u t x

  stretching :=
    mulVortexStretchComponent
      u t x yAxis

  diffusion :=
    mulVorticityDiffusionY u t x

/--
Package the native z-vorticity component as a four-term balance state.
-/
noncomputable def vorticityBalanceStateZ
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState where

  temporal :=
    mulTemporalVorticityZ u t x

  transport :=
    mulVorticityTransportZ u t x

  stretching :=
    mulVortexStretchComponent
      u t x zAxis

  diffusion :=
    mulVorticityDiffusionZ u t x

theorem vorticityBalanceStateX_balanced
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (h : MulVorticityBalanceX u t x) :
    MulBalanceState.Balanced
      (vorticityBalanceStateX u t x) := by

  simpa [
    MulBalanceState.Balanced,
    vorticityBalanceStateX,
    MulVorticityBalanceX
  ] using h

theorem vorticityBalanceStateY_balanced
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (h : MulVorticityBalanceY u t x) :
    MulBalanceState.Balanced
      (vorticityBalanceStateY u t x) := by

  simpa [
    MulBalanceState.Balanced,
    vorticityBalanceStateY,
    MulVorticityBalanceY
  ] using h

theorem vorticityBalanceStateZ_balanced
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (h : MulVorticityBalanceZ u t x) :
    MulBalanceState.Balanced
      (vorticityBalanceStateZ u t x) := by

  simpa [
    MulBalanceState.Balanced,
    vorticityBalanceStateZ,
    MulVorticityBalanceZ
  ] using h

/--
Relative x-vorticity balance state between two native velocity fields.
-/
noncomputable def vorticityBalancePerturbationX
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState :=
  MulBalanceState.ratio
    (vorticityBalanceStateX u t x)
    (vorticityBalanceStateX v t x)

/--
Relative y-vorticity balance state between two native velocity fields.
-/
noncomputable def vorticityBalancePerturbationY
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState :=
  MulBalanceState.ratio
    (vorticityBalanceStateY u t x)
    (vorticityBalanceStateY v t x)

/--
Relative z-vorticity balance state between two native velocity fields.
-/
noncomputable def vorticityBalancePerturbationZ
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (t : ℝ)
    (x : Point3) :
    MulBalanceState :=
  MulBalanceState.ratio
    (vorticityBalanceStateZ u t x)
    (vorticityBalanceStateZ v t x)

/--
Two x-component native vorticity solutions induce a balanced relative
perturbation.
-/
theorem vorticityBalancePerturbationX_balanced
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hu : MulVorticityBalanceX u t x)
    (hv : MulVorticityBalanceX v t x) :
    MulBalanceState.Balanced
      (vorticityBalancePerturbationX u v t x) := by

  unfold vorticityBalancePerturbationX

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateX_balanced hu)
      (vorticityBalanceStateX_balanced hv)

/--
Two y-component native vorticity solutions induce a balanced relative
perturbation.
-/
theorem vorticityBalancePerturbationY_balanced
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hu : MulVorticityBalanceY u t x)
    (hv : MulVorticityBalanceY v t x) :
    MulBalanceState.Balanced
      (vorticityBalancePerturbationY u v t x) := by

  unfold vorticityBalancePerturbationY

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateY_balanced hu)
      (vorticityBalanceStateY_balanced hv)

/--
Two z-component native vorticity solutions induce a balanced relative
perturbation.
-/
theorem vorticityBalancePerturbationZ_balanced
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    (hu : MulVorticityBalanceZ u t x)
    (hv : MulVorticityBalanceZ v t x) :
    MulBalanceState.Balanced
      (vorticityBalancePerturbationZ u v t x) := by

  unfold vorticityBalancePerturbationZ

  exact
    MulBalanceState.ratio_balanced
      (vorticityBalanceStateZ_balanced hu)
      (vorticityBalanceStateZ_balanced hv)

/--
The x-vorticity scale-demand fork specialized to two native balanced fields.
-/
theorem vorticityBalancePerturbationX_failure_forks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (hu : MulVorticityBalanceX u t x)
    (hv : MulVorticityBalanceX v t x)
    (
      hFailure :
        ¬ MulBalanceState.LeftNear
            (vorticityBalancePerturbationX u v t x)
            level
    ) :
    MulBalanceState.LeftFactorFailure
        (vorticityBalancePerturbationX u v t x)
        level
      ∧
    MulBalanceState.RightFactorFailure
        (vorticityBalancePerturbationX u v t x)
        level := by

  exact
    MulBalanceState.balancedFailure_forks
      (vorticityBalancePerturbationX_balanced hu hv)
      hFailure

/--
The y-vorticity scale-demand fork specialized to two native balanced fields.
-/
theorem vorticityBalancePerturbationY_failure_forks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (hu : MulVorticityBalanceY u t x)
    (hv : MulVorticityBalanceY v t x)
    (
      hFailure :
        ¬ MulBalanceState.LeftNear
            (vorticityBalancePerturbationY u v t x)
            level
    ) :
    MulBalanceState.LeftFactorFailure
        (vorticityBalancePerturbationY u v t x)
        level
      ∧
    MulBalanceState.RightFactorFailure
        (vorticityBalancePerturbationY u v t x)
        level := by

  exact
    MulBalanceState.balancedFailure_forks
      (vorticityBalancePerturbationY_balanced hu hv)
      hFailure

/--
The z-vorticity scale-demand fork specialized to two native balanced fields.
-/
theorem vorticityBalancePerturbationZ_failure_forks
    {
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {t : ℝ}
    {x : Point3}
    {level : Depth}
    (hu : MulVorticityBalanceZ u t x)
    (hv : MulVorticityBalanceZ v t x)
    (
      hFailure :
        ¬ MulBalanceState.LeftNear
            (vorticityBalancePerturbationZ u v t x)
            level
    ) :
    MulBalanceState.LeftFactorFailure
        (vorticityBalancePerturbationZ u v t x)
        level
      ∧
    MulBalanceState.RightFactorFailure
        (vorticityBalancePerturbationZ u v t x)
        level := by

  exact
    MulBalanceState.balancedFailure_forks
      (vorticityBalancePerturbationZ_balanced hu hv)
      hFailure

end Euclidean
end Bridge

end PrimeTensor
