import PrimeTensor.Fluid.VorticityL1LinfControl

/-!
# Preterminal Navier--Stokes fields and continuation extensions

The cascade modules are terminal-state statements: they compare preterminal
states with a field value at a candidate terminal time `T`.

A genuine continuation theorem, however, starts from a solution defined only
on the open interval `(0,T)` and proves that it extends smoothly through `T`.
Using a globally regular field as the input admissibility predicate would
therefore assume the conclusion.

This file separates those two roles.

* `PreterminalNavierStokes3 v p T` describes a real velocity/pressure pair only
  on `0 < t < T`, including the genuine mixed spacetime derivative witnesses
  needed by the curl calculation.
* `LoggedPreterminalNavierStokesAdmissible u T` says that the logged native
  velocity is such a preterminal solution for some real pressure.
* `AgreesBeforeT u v T` says that two native spacetime velocity fields agree
  throughout the preterminal interval.
* `SmoothContinuationExtension u v T` says that `v` agrees with the
  preterminal field `u` before `T` and has exactly the spatial/temporal jet
  regularity needed by the terminal cascade at `T`.

No existence theorem for `v` is asserted here.  Producing such a continuation
extension from the vorticity `L¹_t L∞_x` control is the genuine classical PDE
step still to be formalized.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Separated regularity for a classical velocity/pressure pair only on the open
preterminal interval `(0,T)`.

Spatial regularity is stated slice-by-slice.  Time regularity is `C¹` on the
open interval, componentwise.  The mixed time/space commutation required by
the vorticity equation is included only at preterminal times.
-/
structure PreterminalVorticityRegularity3
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (T : ℝ) : Prop where

  velocity_spatial_three :
    ∀ (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      ∀ (j : PrimeTensor.Axis Depth.three),
        SpatialC3
          (
            fun x =>
              (v t x).component j
          )

  velocity_temporal_one :
    ∀ (x : Point3)
      (j : PrimeTensor.Axis Depth.three),
      ContDiffOn
        ℝ 1
        (
          fun t =>
            (v t x).component j
        )
        (Set.Ioo (0 : ℝ) T)

  pressure_spatial_two :
    ∀ (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      SpatialC2
        (p t)

  /--
  Genuine mixed spacetime derivative witness at every preterminal time.

  This is intentionally a `HasDerivAt`, not merely the resulting derivative
  equality.  The temporal operator is Mathlib's total `deriv`, so the curl
  calculation needs this witness to differentiate the subtraction defining
  vorticity without relying on fallback derivative values.
  -/
  velocity_space_time_hasDerivAt :
    ∀ (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      ∀
        (x : Point3)
        (i j : PrimeTensor.Axis Depth.three),
        HasDerivAt
          (
            fun τ =>
              spatial3.d
                i
                (
                  fun y =>
                    (v τ y).component j
                )
                x
          )
          (
            spatial3.d
              i
              (
                fun y =>
                  temporal.d
                    (
                      fun τ =>
                        (v τ y).component j
                    )
                    t
              )
              x
          )
          t

/--
Normalized incompressible Navier--Stokes equations restricted to the open
preterminal interval `(0,T)`.
-/
structure PreterminalNavierStokes3
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    )
    (T : ℝ) : Prop where

  positive_terminal :
    0 < T

  regularity :
    PreterminalVorticityRegularity3
      v p T

  incompressible :
    ∀ (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      ∀ (x : Point3),
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3
            (v t)
            x
          =
        0

  momentum :
    ∀ (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      ∀
        (x : Point3)
        (j : PrimeTensor.Axis Depth.three),
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal v t x
        ).component j
          +
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3 v t x
        ).component j
          =
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3 p t x j
          +
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3 v t x
        ).component j

/--
The logged native velocity is an admissible classical Navier--Stokes velocity
on `(0,T)` for some real pressure.

Nothing is assumed about the field at `T` or after `T`.
-/
def LoggedPreterminalNavierStokesAdmissible
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∃
    p :
      PrimeTensor.SpaceTimeScalarField
        ℝ ℝ ℝ Depth.three,
    PreterminalNavierStokes3
      (PrimeTensor.Bridge.logSpaceTimeVectorField u)
      p
      T

/--
Two native velocity fields agree throughout the preterminal interval.

The fields remain total functions on real time for compatibility with the
existing calculus API, but no equality is required at `T` or after it.
-/
def AgreesBeforeT
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∀ (t : ℝ),
    t ∈ Set.Ioo (0 : ℝ) T →
    u t = v t

/--
A time-refinement path approaches `T` strictly from within the preterminal
interval.
-/
def TimePathStrictlyBefore
    (
      τ : TimeRefinementSeq
    )
    (T : ℝ) : Prop :=
  ∀ n : Depth,
    τ n ∈ Set.Ioo (0 : ℝ) T

/--
The three native vorticity balances hold at the terminal time.

A genuine Navier--Stokes continuation through `T` supplies this automatically;
recording it here is necessary because the terminal cascade theorems explicitly
take the limiting balance as an input.
-/
def TerminalVorticityBalanced
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  ∀ x : Point3,
    MulVorticityBalanceX v T x
      ∧
    MulVorticityBalanceY v T x
      ∧
    MulVorticityBalanceZ v T x

/--
The exact terminal regularity package required by the current multiplicative
cascade after a continuation has been constructed.

This is intentionally a predicate on the extension `v`, not on the original
preterminal field `u`.
-/
def TerminalCascadeRegular
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop :=
  VelocityLogSpatialC3 v
    ∧
  ∀ x : Point3,
    ¬ VelocityJetFailureAt v T x

/--
A smooth Navier--Stokes continuation extension of a preterminal native velocity
field.

`v` agrees with `u` before `T`, satisfies all three native vorticity balances
at `T`, and carries the terminal regularity required by the already-proved
cascade obstruction.
-/
structure SmoothContinuationExtension
    (
      u v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ) : Prop where

  agrees_before :
    AgreesBeforeT u v T

  terminal_balanced :
    TerminalVorticityBalanced v T

  terminal_regular :
    TerminalCascadeRegular v T

/--
The genuine continuation-existence statement associated with the concrete
vorticity control.

This is the correct non-circular analytic target:

    preterminal Navier--Stokes
      + vorticity L¹_t L∞_x control
      -> existence of a smooth extension through T.
-/
def VorticityL1LinfProducesExtension : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible u T →
      VorticityL1LinfControl u T →
      ∃
        v :
          PrimeTensor.SpaceTimeVectorField
            ℝ ℝ PrimeTensor.MulReal Depth.three,
        SmoothContinuationExtension
          u v T

/--
Every global vorticity-regular classical solution restricts to a preterminal
solution on every positive terminal interval.

This theorem is only a consistency check for the new interval predicate; its
converse is intentionally not claimed.
-/
theorem preterminalNavierStokes3_of_vorticitySolution
    (s : VorticitySolution3)
    {T : ℝ}
    (hT : 0 < T) :
    PreterminalNavierStokes3
      s.velocity
      s.pressure
      T := by

  refine
    {
      positive_terminal := hT
      regularity := ?_
      incompressible := ?_
      momentum := ?_
    }

  · refine
      {
        velocity_spatial_three := ?_
        velocity_temporal_one := ?_
        pressure_spatial_two := ?_
        velocity_space_time_hasDerivAt := ?_
      }

    · intro t ht j

      exact
        s.regularity.velocity_spatial_three
          t j

    · intro x j

      have hGlobal :
          TemporalC1
            (
              fun t =>
                (s.velocity t x).component j
            ) :=
        s.solution.regularity.velocity_temporal
          x j

      unfold TemporalC1 at hGlobal

      exact
        hGlobal.contDiffOn

    · intro t ht

      exact
        s.regularity.pressure_spatial_two
          t

    · intro t ht x i j

      exact
        s.velocity_space_time_hasDerivAt
          t x i j

  · intro t ht x

    exact
      s.solution.incompressible_xyz
        t x

  · intro t ht x j

    exact
      s.solution.momentum_xyz
        t x j

end Euclidean
end Bridge
end PrimeTensor
