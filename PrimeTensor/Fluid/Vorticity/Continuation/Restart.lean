import PrimeTensor.Fluid.Vorticity.Continuation.Frontier
import PrimeTensor.Fluid.Vorticity.Preterminal.Equation
import PrimeTensor.Fluid.Vorticity.Jet.Failure
import PrimeTensor.Bridge.Log.Surjective

/-!
# Real-coordinate H³ restart bridge

The remaining continuation theorem is classical.  It should therefore be
stated in ordinary real logarithmic coordinates rather than on the native
`MulReal` carrier.

The completed logarithmic coordinate is already an equivalence

    MulReal.logEquiv : MulReal ≃ ℝ.

This file lifts an arbitrary real spacetime velocity field back to a native
field componentwise and proves that logging the lift recovers the original
real field exactly.

Consequently, a classical Navier--Stokes restart past `T` can be stated entirely
for a real velocity/pressure pair.  The existing native vorticity bridge then
supplies terminal multiplicative balance automatically after lifting.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/--
Two tensors are equal when all of their components are equal.

The project tensor is a one-field structure, but no generated/extensionality
lemma is currently exposed under `PrimeTensor.Tensor.ext`, so keep this tiny
componentwise bridge local to the continuation module.
-/
theorem tensor_eq_of_component_eq
    {A : Type}
    {dim rank : Depth}
    {s t : PrimeTensor.Tensor A dim rank}
    (
      h :
        ∀ i : PrimeTensor.IndexTuple dim rank,
          s.component i = t.component i
    ) :
    s = t := by

  rcases s with ⟨sc⟩
  rcases t with ⟨tc⟩

  congr 1

  funext i

  exact h i

/--
Componentwise inverse-log lift of a real vector field to the native completed
multiplicative carrier.
-/
noncomputable def nativeVectorFieldOfReal
    {X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.VectorField
          X ℝ dim
    ) :
    PrimeTensor.VectorField
      X PrimeTensor.MulReal dim :=
  fun x =>
    ⟨
      fun i =>
        PrimeTensor.Bridge.MulReal.logEquiv.symm
          ((u x).component i)
    ⟩

/--
Logging the native lift of a real vector field recovers the original real
vector field exactly.
-/
@[simp]
theorem logVectorField_nativeVectorFieldOfReal
    {X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.VectorField
          X ℝ dim
    ) :
    PrimeTensor.Bridge.logVectorField
        (nativeVectorFieldOfReal u)
      =
    u := by

  funext x

  apply tensor_eq_of_component_eq

  intro i

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.Bridge.MulReal.logEquiv.symm
            ((u x).component i)
        )
      =
    (u x).component i

  exact
    PrimeTensor.Bridge.MulReal.logEquiv.apply_symm_apply
      ((u x).component i)

/--
Inverse direction: lifting the logged coordinates of a native vector field
recovers that native vector field.
-/
@[simp]
theorem nativeVectorFieldOfReal_logVectorField
    {X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.VectorField
          X PrimeTensor.MulReal dim
    ) :
    nativeVectorFieldOfReal
        (PrimeTensor.Bridge.logVectorField u)
      =
    u := by

  funext x

  apply tensor_eq_of_component_eq

  intro i

  change
    PrimeTensor.Bridge.MulReal.logEquiv.symm
        (
          PrimeTensor.Bridge.MulReal.logValue
            ((u x).component i)
        )
      =
    (u x).component i

  change
    PrimeTensor.Bridge.MulReal.logEquiv.symm
        (
          PrimeTensor.Bridge.MulReal.logEquiv
            ((u x).component i)
        )
      =
    (u x).component i

  exact
    PrimeTensor.Bridge.MulReal.logEquiv.symm_apply_apply
      ((u x).component i)

/--
Componentwise inverse-log lift of a real spacetime velocity field.
-/
noncomputable def nativeSpaceTimeVectorFieldOfReal
    {T X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          T X ℝ dim
    ) :
    PrimeTensor.SpaceTimeVectorField
      T X PrimeTensor.MulReal dim :=
  fun t =>
    nativeVectorFieldOfReal
      (u t)

/--
Logging a lifted real spacetime velocity field is exactly the original real
field.
-/
@[simp]
theorem logSpaceTimeVectorField_nativeSpaceTimeVectorFieldOfReal
    {T X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          T X ℝ dim
    ) :
    PrimeTensor.Bridge.logSpaceTimeVectorField
        (nativeSpaceTimeVectorFieldOfReal u)
      =
    u := by

  funext t

  exact
    logVectorField_nativeVectorFieldOfReal
      (u t)

/--
Lifting the logarithmic coordinates of a native spacetime velocity field
recovers the original native field.
-/
@[simp]
theorem nativeSpaceTimeVectorFieldOfReal_logSpaceTimeVectorField
    {T X : Type}
    {dim : Depth}
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          T X PrimeTensor.MulReal dim
    ) :
    nativeSpaceTimeVectorFieldOfReal
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField u
        )
      =
    u := by

  funext t

  exact
    nativeVectorFieldOfReal_logVectorField
      (u t)

/--
A real restart field agrees with the original native field before `T` when its
real values are exactly the logged native values there.
-/
def RealRestartAgreesBeforeT
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (T : ℝ) : Prop :=
  ∀ t : ℝ,
    t ∈ Set.Ioo (0 : ℝ) T →
      PrimeTensor.Bridge.logSpaceTimeVectorField
          u t
        =
      v t

/--
Real-coordinate agreement before `T` becomes ordinary native agreement after
inverse-log lifting.
-/
theorem agreesBeforeT_nativeSpaceTimeVectorFieldOfReal
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {T : ℝ}
    (
      hAgree :
        RealRestartAgreesBeforeT
          u v T
    ) :
    AgreesBeforeT
      u
      (nativeSpaceTimeVectorFieldOfReal v)
      T := by

  intro t ht

  have h :=
    congrArg
      nativeVectorFieldOfReal
      (hAgree t ht)

  change
    nativeVectorFieldOfReal
        (
          PrimeTensor.Bridge.logVectorField
            (u t)
        )
      =
    nativeVectorFieldOfReal
      (v t)
    at h

  change
    u t
      =
    nativeVectorFieldOfReal
      (v t)

  rw [
    ← nativeVectorFieldOfReal_logVectorField
        (u t)
  ]

  exact h

/--
Global slice-wise spatial `C³` regularity for an ordinary real velocity field.

This is only a representation/package condition for the current total-field
continuation API.  The actual local Navier--Stokes restart theorem needs
spatial `C³` only on its existence interval; values outside that interval can
be filled by arbitrary spatially smooth slices.
-/
def RealVelocitySpatialC3
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    ) : Prop :=
  ∀
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three),
      SpatialC3
        (
          fun y =>
            (v t y).component j
        )

/--
Time continuity at `(T,x)` of the complete third spatial jet of an ordinary
real velocity field.
-/
def RealVelocityThirdJetContinuousAt
    (
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (T : ℝ)
    (x : Point3) : Prop :=
  ∀
    (a b c j :
      PrimeTensor.Axis Depth.three),
    ContinuousAt
      (
        fun t =>
          spatial3.d
            a
            (
              spatial3.d
                b
                (
                  spatial3.d
                    c
                    (
                      fun y =>
                        (v t y).component j
                    )
                )
            )
            x
      )
      T

/--
Real slice-wise spatial `C³` regularity becomes the native logged spatial
regularity required by the current continuation object.
-/
theorem velocityLogSpatialC3_nativeSpaceTimeVectorFieldOfReal
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    (
      hSpatial :
        RealVelocitySpatialC3
          v
    ) :
    VelocityLogSpatialC3
      (nativeSpaceTimeVectorFieldOfReal v) := by

  unfold VelocityLogSpatialC3

  rw [
    logSpaceTimeVectorField_nativeSpaceTimeVectorFieldOfReal
      v
  ]

  simpa [
    RealVelocitySpatialC3
  ] using hSpatial

/--
Real third-jet time continuity is exactly the logged third-jet continuity of
the inverse-log lift.
-/
theorem velocityThirdJetLogContinuousAt_nativeSpaceTimeVectorFieldOfReal
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hThird :
        RealVelocityThirdJetContinuousAt
          v T x
    ) :
    VelocityThirdJetLogContinuousAt
      (nativeSpaceTimeVectorFieldOfReal v)
      T x := by

  unfold VelocityThirdJetLogContinuousAt

  rw [
    logSpaceTimeVectorField_nativeSpaceTimeVectorFieldOfReal
      v
  ]

  simpa [
    RealVelocityThirdJetContinuousAt
  ] using hThird

/--
A real preterminal Navier--Stokes solution becomes a logged-native preterminal
solution after inverse-log lifting.
-/
theorem loggedPreterminalNavierStokesAdmissible_nativeSpaceTimeVectorFieldOfReal
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {S : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p S
    ) :
    LoggedPreterminalNavierStokesAdmissible
      (nativeSpaceTimeVectorFieldOfReal v)
      S := by

  refine
    ⟨
      p,
      ?_
    ⟩

  simpa using s

/--
The complete first logged spatial jet of the lifted restart is time-continuous
at every interior restart time.  This is already contained in
`PreterminalVorticityRegularity3.velocity_space_time_hasDerivAt`.
-/
theorem velocityFirstJetLogContinuousAt_of_realRestart
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {S T : ℝ}
    (
      s :
        PreterminalNavierStokes3
          v p S
    )
    (
      hT :
        T ∈ Set.Ioo (0 : ℝ) S
    )
    (x : Point3) :
    VelocityFirstJetLogContinuousAt
      (nativeSpaceTimeVectorFieldOfReal v)
      T x := by

  intro i j

  have h :
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
                  T
            )
            x
        )
        T :=
    s.regularity.velocity_space_time_hasDerivAt
      T hT x i j

  simpa [
    PrimeTensor.Bridge.logSpaceTimeVectorField,
    nativeSpaceTimeVectorFieldOfReal,
    nativeVectorFieldOfReal
  ] using h.continuousAt

/--
First- and third-jet time continuity excludes the explicit terminal
`VelocityJetFailureAt` predicate.
-/
theorem not_velocityJetFailureAt_of_first_and_third
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {T : ℝ}
    {x : Point3}
    (
      hFirst :
        VelocityFirstJetLogContinuousAt
          v T x
    )
    (
      hThird :
        VelocityThirdJetLogContinuousAt
          v T x
    ) :
    ¬ VelocityJetFailureAt
        v T x := by

  intro hFailure

  rcases hFailure with
    hFirstFailure | hThirdFailure

  · exact hFirstFailure hFirst
  · exact hThirdFailure hThird

/--
A real restart extending strictly beyond `T` produces the existing native
`SmoothContinuationExtension` object after inverse-log lifting.

The terminal multiplicative vorticity balance is derived from the restarted
real Navier--Stokes equation, rather than included as an independent restart
hypothesis.
-/
theorem smoothContinuationExtension_of_realRestart
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {
      v :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    }
    {
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    }
    {S T : ℝ}
    (
      hAgree :
        RealRestartAgreesBeforeT
          u v T
    )
    (
      s :
        PreterminalNavierStokes3
          v p S
    )
    (
      hT :
        T ∈ Set.Ioo (0 : ℝ) S
    )
    (
      hSpatial :
        RealVelocitySpatialC3
          v
    )
    (
      hThird :
        ∀ x : Point3,
          RealVelocityThirdJetContinuousAt
            v T x
    ) :
    SmoothContinuationExtension
      u
      (nativeSpaceTimeVectorFieldOfReal v)
      T := by

  have hAdmissible :
      LoggedPreterminalNavierStokesAdmissible
        (nativeSpaceTimeVectorFieldOfReal v)
        S :=
    loggedPreterminalNavierStokesAdmissible_nativeSpaceTimeVectorFieldOfReal
      s

  refine
    ⟨
      agreesBeforeT_nativeSpaceTimeVectorFieldOfReal
        hAgree,
      ?_,
      ?_
    ⟩

  · intro x

    exact
      mulVorticityBalance3_of_loggedPreterminalNavierStokes
        hAdmissible
        hT

  · refine
      ⟨
        velocityLogSpatialC3_nativeSpaceTimeVectorFieldOfReal
          hSpatial,
        ?_
      ⟩

    intro x

    have hFirst :
        VelocityFirstJetLogContinuousAt
          (nativeSpaceTimeVectorFieldOfReal v)
          T x :=
      velocityFirstJetLogContinuousAt_of_realRestart
        s
        hT
        x

    have hThirdNative :
        VelocityThirdJetLogContinuousAt
          (nativeSpaceTimeVectorFieldOfReal v)
          T x :=
      velocityThirdJetLogContinuousAt_nativeSpaceTimeVectorFieldOfReal
        (hThird x)

    exact
      not_velocityJetFailureAt_of_first_and_third
        hFirst
        hThirdNative

/--
The remaining classical H³ restart theorem, stated in ordinary real
coordinates.

Given a logged preterminal Navier--Stokes solution with uniform terminal-tail
H³ control, produce a real Navier--Stokes restart on a strictly larger interval
`(0,S)` which agrees with the old logged solution before `T`.

The two genuinely analytic outputs beyond local existence are:

* spatial `C³` slice regularity for the total-field representation;
* time continuity of the complete third spatial jet at the crossing time `T`.

The former is harmless total-function packaging outside the local existence
interval; the latter is the actual parabolic smoothing/time-regularity datum.
-/
def H3ControlProducesRealRestart : Prop :=
  ∀
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    )
    (T : ℝ),
      LoggedPreterminalNavierStokesAdmissible
          u T
        →
      TerminalTailH3Control
          u T
        →
      ∃
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
        (S : ℝ),
          T < S
            ∧
          RealRestartAgreesBeforeT
            u v T
            ∧
          PreterminalNavierStokes3
            v p S
            ∧
          RealVelocitySpatialC3
            v
            ∧
          (
            ∀ x : Point3,
              RealVelocityThirdJetContinuousAt
                v T x
          )

/--
The real-coordinate H³ restart theorem discharges the previously isolated
`H3ControlProducesExtension` continuation frontier.
-/
theorem h3ControlProducesExtension_of_realRestart
    (
      hRestart :
        H3ControlProducesRealRestart
    ) :
    H3ControlProducesExtension := by

  intro
    u T
    hAdmissible
    hH3

  have hTPositive :
      0 < T := by

    rcases hH3 with
      ⟨
        a,
        M,
        ha,
        hM,
        hBound
      ⟩

    exact
      lt_trans
        ha.1
        ha.2

  obtain
    ⟨
      v,
      p,
      S,
      hTS,
      hAgree,
      s,
      hSpatial,
      hThird
    ⟩ :=
      hRestart
        u T
        hAdmissible
        hH3

  refine
    ⟨
      nativeSpaceTimeVectorFieldOfReal v,
      smoothContinuationExtension_of_realRestart
        hAgree
        s
        ?_
        hSpatial
        hThird
    ⟩

  exact
    ⟨
      hTPositive,
      hTS
    ⟩

end Euclidean
end Bridge
end PrimeTensor
