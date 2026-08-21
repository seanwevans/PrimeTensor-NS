import PrimeTensor.Bridge.MulReal.Log.Algebra
import PrimeTensor.Bridge.Fluid.Kernel

/-!
# Log-coordinate semantics of the canonical multiplicative fluid system

The completed scalar algebra is now fully understood under

    L := MulReal.logValue.

This file conjugates the canonical multiplicative fluid equations into an
ordinary real-coordinate system.

There is one deliberately explicit remaining analytic interface:

* `SpatialLogCompatible D DR` says the ordinary real directional derivative
  of a logged field agrees with the log of the intrinsic multiplicative
  directional derivative;
* `TemporalLogCompatible Dt DtR` says the same for time.

No such compatibility is assumed silently.

Under those hypotheses:

* intrinsic incompressibility becomes additive divergence zero;
* the canonical completed coupling becomes ordinary multiplication;
* the multiplicative momentum balance becomes the normalized real equation

      ∂ₜv + (v · ∇)v = -∇π + Δv

  componentwise, where `v = L ∘ u` and `π = L ∘ p`.

The real derivative interfaces are still abstract `Differential` /
`TemporalDifferential` structures.  A later analytic bridge can instantiate
them with conventional derivatives.
-/

namespace PrimeTensor
namespace Bridge

/--
The logarithm of a nonempty multiplicative axis fold is the corresponding
nonempty additive real fold.
-/
theorem logValue_axisFold :
    ∀ (dim : Depth)
      (f : PrimeTensor.Axis dim → PrimeTensor.MulReal),
      PrimeTensor.Bridge.MulReal.logValue
          (PrimeTensor.Axis.fold (· * ·) dim f)
        =
      PrimeTensor.Axis.fold (· + ·) dim
        (fun i =>
          PrimeTensor.Bridge.MulReal.logValue (f i))

  | .one, f => by
      rfl

  | .succ d, f => by
      change
        PrimeTensor.Bridge.MulReal.logValue
            (
              f .first *
                PrimeTensor.Axis.fold (· * ·) d
                  (fun i => f (.next i))
            )
          =
        PrimeTensor.Bridge.MulReal.logValue
              (f .first) +
          PrimeTensor.Axis.fold (· + ·) d
            (fun i =>
              PrimeTensor.Bridge.MulReal.logValue
                (f (.next i)))

      rw [
        PrimeTensor.Bridge.MulReal.logValue_mul,
        logValue_axisFold d
          (fun i => f (.next i))
      ]

/-- Log-coordinate scalar field. -/
noncomputable def logScalarField
    {X : Type} {dim : Depth}
    (f : PrimeTensor.ScalarField
      X PrimeTensor.MulReal dim) :
    PrimeTensor.ScalarField X ℝ dim :=
  fun x =>
    PrimeTensor.Bridge.MulReal.logValue (f x)

/-- Log-coordinate vector field. -/
noncomputable def logVectorField
    {X : Type} {dim : Depth}
    (u : PrimeTensor.VectorField
      X PrimeTensor.MulReal dim) :
    PrimeTensor.VectorField X ℝ dim :=
  fun x =>
    ⟨fun i =>
      PrimeTensor.Bridge.MulReal.logValue
        ((u x).component i)⟩

/-- Log-coordinate spacetime scalar field. -/
noncomputable def logSpaceTimeScalarField
    {T X : Type} {dim : Depth}
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X PrimeTensor.MulReal dim) :
    PrimeTensor.SpaceTimeScalarField
      T X ℝ dim :=
  fun t =>
    logScalarField (p t)

/-- Log-coordinate spacetime vector field. -/
noncomputable def logSpaceTimeVectorField
    {T X : Type} {dim : Depth}
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim) :
    PrimeTensor.SpaceTimeVectorField
      T X ℝ dim :=
  fun t =>
    logVectorField (u t)

/--
Compatibility between the intrinsic spatial differential and a conventional
real directional differential after logarithmic conjugation.
-/
structure SpatialLogCompatible
    {X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (DR :
      PrimeTensor.Differential
        X ℝ dim) : Prop where

  d_log :
    ∀ (i : PrimeTensor.Axis dim)
      (f :
        PrimeTensor.ScalarField
          X PrimeTensor.MulReal dim)
      (x : PrimeTensor.Point X dim),
      DR.d i
          (fun y =>
            PrimeTensor.Bridge.MulReal.logValue
              (f y))
          x
        =
      PrimeTensor.Bridge.MulReal.logValue
        (D.d i f x)

/--
Compatibility between the intrinsic temporal differential and a conventional
real temporal differential after logarithmic conjugation.
-/
structure TemporalLogCompatible
    {T : Type}
    (Dt :
      PrimeTensor.TemporalDifferential
        T PrimeTensor.MulReal)
    (DtR :
      PrimeTensor.TemporalDifferential
        T ℝ) : Prop where

  d_log :
    ∀ (f : T → PrimeTensor.MulReal)
      (t : T),
      DtR.d
          (fun s =>
            PrimeTensor.Bridge.MulReal.logValue
              (f s))
          t
        =
      PrimeTensor.Bridge.MulReal.logValue
        (Dt.d f t)

namespace SpatialLogCompatible

theorem d_log_field
    {X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (i : PrimeTensor.Axis dim)
    (f :
      PrimeTensor.ScalarField
        X PrimeTensor.MulReal dim) :
    DR.d i
        (fun y =>
          PrimeTensor.Bridge.MulReal.logValue
            (f y))
      =
    fun x =>
      PrimeTensor.Bridge.MulReal.logValue
        (D.d i f x) := by

  funext x

  exact hD.d_log i f x

/--
Compatibility iterates to same-axis second derivatives.
-/
theorem d2_log
    {X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (i : PrimeTensor.Axis dim)
    (f :
      PrimeTensor.ScalarField
        X PrimeTensor.MulReal dim)
    (x : PrimeTensor.Point X dim) :
    DR.d i
        (
          DR.d i
            (fun y =>
              PrimeTensor.Bridge.MulReal.logValue
                (f y))
        )
        x
      =
    PrimeTensor.Bridge.MulReal.logValue
      (D.d i (D.d i f) x) := by

  rw [hD.d_log_field i f]

  exact
    hD.d_log i (D.d i f) x

end SpatialLogCompatible

namespace RealFluid

/-- Ordinary additive real divergence over the positive axis. -/
def divergence
    {X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (u :
      PrimeTensor.VectorField
        X ℝ dim) :
    PrimeTensor.ScalarField
      X ℝ dim :=
  fun x =>
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        D.d i
          (fun y => (u y).component i)
          x)

/-- Ordinary additive real Laplacian over the positive axis. -/
def laplacian
    {X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (f :
      PrimeTensor.ScalarField
        X ℝ dim) :
    PrimeTensor.ScalarField
      X ℝ dim :=
  fun x =>
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        D.d i (D.d i f) x)

/-- Componentwise real Laplacian of a spacetime vector field. -/
def laplacianVector
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X ℝ dim) :
    PrimeTensor.SpaceTimeVectorField
      T X ℝ dim :=
  fun t x =>
    ⟨fun j =>
      laplacian D
        (fun y => (u t y).component j)
        x⟩

/-- Ordinary real advection `(u · ∇)u`. -/
def advection
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X ℝ dim) :
    PrimeTensor.SpaceTimeVectorField
      T X ℝ dim :=
  fun t x =>
    ⟨fun j =>
      PrimeTensor.Axis.fold (· + ·) dim
        (fun i =>
          (u t x).component i *
            D.d i
              (fun y => (u t y).component j)
              x)⟩

/-- Componentwise temporal derivative of a real spacetime vector field. -/
def temporalVectorDerivative
    {T X : Type} {dim : Depth}
    (Dt :
      PrimeTensor.TemporalDifferential
        T ℝ)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X ℝ dim) :
    PrimeTensor.SpaceTimeVectorField
      T X ℝ dim :=
  fun t x =>
    ⟨fun j =>
      Dt.d
        (fun s => (u s x).component j)
        t⟩

/-- Conventional negative pressure-gradient component. -/
def pressureForceComponent
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X ℝ dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) : ℝ :=
  -
    D.d j (p t) x

/-- Additive real incompressibility. -/
def Incompressible
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X ℝ dim) : Prop :=
  ∀ t x,
    divergence D (u t) x = 0

/--
Normalized additive real momentum balance in the positive-dimensional axis
formalism.
-/
def MomentumBalance
    {T X : Type} {dim : Depth}
    (Dt :
      PrimeTensor.TemporalDifferential
        T ℝ)
    (D :
      PrimeTensor.Differential
        X ℝ dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X ℝ dim)
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X ℝ dim) : Prop :=
  ∀ t x (j : PrimeTensor.Axis dim),
    (temporalVectorDerivative Dt u t x).component j +
        (advection D u t x).component j
      =
    pressureForceComponent D p t x j +
      (laplacianVector D u t x).component j

structure Solution
    {T X : Type} {dim : Depth}
    (Dt :
      PrimeTensor.TemporalDifferential
        T ℝ)
    (D :
      PrimeTensor.Differential
        X ℝ dim) where

  velocity :
    PrimeTensor.SpaceTimeVectorField
      T X ℝ dim

  pressure :
    PrimeTensor.SpaceTimeScalarField
      T X ℝ dim

  incompressible :
    Incompressible D velocity

  momentum :
    MomentumBalance Dt D velocity pressure

end RealFluid

/--
Logarithmic semantics of intrinsic multiplicative divergence.
-/
theorem logValue_divergence
    {X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (u :
      PrimeTensor.VectorField
        X PrimeTensor.MulReal dim)
    (x : PrimeTensor.Point X dim) :
    PrimeTensor.Bridge.MulReal.logValue
        (D.divergence u x)
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (fun y => (u y).component i)
              x
          )) := by

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.Axis.fold (· * ·) dim
            (fun i =>
              D.d i
                (fun y => (u y).component i)
                x)
        )
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (fun y => (u y).component i)
              x
          ))

  exact
    logValue_axisFold dim
      (fun i =>
        D.d i
          (fun y => (u y).component i)
          x)

/--
Logarithmic semantics of the intrinsic multiplicative vector Laplacian.
-/
theorem logValue_laplacianVector_component
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          (PrimeTensor.MulFluid.laplacianVector
            D u t x).component j
        )
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (
                D.d i
                  (fun y => (u t y).component j)
              )
              x
          )) := by

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.Axis.fold (· * ·) dim
            (fun i =>
              D.d i
                (
                  D.d i
                    (fun y => (u t y).component j)
                )
                x)
        )
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (
                D.d i
                  (fun y => (u t y).component j)
              )
              x
          ))

  exact
    logValue_axisFold dim
      (fun i =>
        D.d i
          (
            D.d i
              (fun y => (u t y).component j)
          )
          x)

/--
Logarithmic semantics of the multiplicative inverse pressure gradient.
-/
theorem logValue_pressureForce_component
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          (PrimeTensor.MulFluid.pressureForce
            D p t x).component j
        )
      =
    -
      PrimeTensor.Bridge.MulReal.logValue
        (D.d j (p t) x) := by

  change
    PrimeTensor.Bridge.MulReal.logValue
        ((D.d j (p t) x)⁻¹)
      =
    -
      PrimeTensor.Bridge.MulReal.logValue
        (D.d j (p t) x)

  exact
    PrimeTensor.Bridge.MulReal.logValue_inv
      (D.d j (p t) x)

/--
Logarithmic semantics of the canonical nonlinear contraction.
-/
theorem logValue_logProductAdvectionFold
    {T X : Type} {dim : Depth}
    (D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.Axis.fold (· * ·) dim
            (fun i =>
              PrimeTensor.Bridge.PrimePairApprox.logProductCoupling.couple
                  ((u t x).component i)
                  (
                    D.d i
                      (fun y => (u t y).component j)
                      x
                  ))
        )
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
              ((u t x).component i) *
          PrimeTensor.Bridge.MulReal.logValue
            (
              D.d i
                (fun y => (u t y).component j)
                x
            )) := by

  rw [logValue_axisFold]

  apply congrArg
    (PrimeTensor.Axis.fold (· + ·) dim)

  funext i

  exact
    PrimeTensor.Bridge.PrimePairApprox.logProductCoupling_logValue
      ((u t x).component i)
        (
          D.d i
            (fun y => (u t y).component j)
            x
        )

/--
A compatible real derivative turns intrinsic log-divergence exactly into
ordinary additive divergence of the log-coordinate vector field.
-/
theorem realDivergence_logField
    {X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (u :
      PrimeTensor.VectorField
        X PrimeTensor.MulReal dim)
    (x : PrimeTensor.Point X dim) :
    RealFluid.divergence
        DR
        (logVectorField u)
        x
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (fun y => (u y).component i)
              x
          )) := by

  unfold RealFluid.divergence
  unfold logVectorField

  apply congrArg
    (PrimeTensor.Axis.fold (· + ·) dim)

  funext i

  exact
    hD.d_log i
      (fun y => (u y).component i)
      x

/--
A compatible real derivative turns the logarithmic intrinsic second-derivative
fold into the ordinary additive Laplacian.
-/
theorem realLaplacianVector_logField
    {T X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    (
      RealFluid.laplacianVector
        DR
        (logSpaceTimeVectorField u)
        t x
    ).component j
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
          (
            D.d i
              (
                D.d i
                  (fun y => (u t y).component j)
              )
              x
          )) := by

  unfold RealFluid.laplacianVector
  unfold RealFluid.laplacian
  unfold logSpaceTimeVectorField
  unfold logVectorField

  apply congrArg
    (PrimeTensor.Axis.fold (· + ·) dim)

  funext i

  exact
    hD.d2_log i
      (fun y => (u t y).component j)
      x

/--
A compatible real derivative turns the logarithmic canonical advection fold
into ordinary `(v · ∇)v` for the logged velocity field.
-/
theorem realAdvection_logField
    {T X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    (
      RealFluid.advection
        DR
        (logSpaceTimeVectorField u)
        t x
    ).component j
      =
    PrimeTensor.Axis.fold (· + ·) dim
      (fun i =>
        PrimeTensor.Bridge.MulReal.logValue
              ((u t x).component i) *
          PrimeTensor.Bridge.MulReal.logValue
            (
              D.d i
                (fun y => (u t y).component j)
                x
            )) := by

  unfold RealFluid.advection
  unfold logSpaceTimeVectorField
  unfold logVectorField

  apply congrArg
    (PrimeTensor.Axis.fold (· + ·) dim)

  funext i

  rw [
    hD.d_log i
      (fun y => (u t y).component j)
      x
  ]

/--
A compatible real time differential turns the intrinsic temporal response into
the ordinary derivative of the logged velocity component.
-/
theorem realTemporalDerivative_logField
    {T X : Type} {dim : Depth}
    {Dt :
      PrimeTensor.TemporalDifferential
        T PrimeTensor.MulReal}
    {DtR :
      PrimeTensor.TemporalDifferential
        T ℝ}
    (hDt : TemporalLogCompatible Dt DtR)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    (
      RealFluid.temporalVectorDerivative
        DtR
        (logSpaceTimeVectorField u)
        t x
    ).component j
      =
    PrimeTensor.Bridge.MulReal.logValue
      (
        (Dt.vectorDerivative u t x).component j
      ) := by

  change
    DtR.d
        (
          fun s =>
            PrimeTensor.Bridge.MulReal.logValue
              ((u s x).component j)
        )
        t
      =
    PrimeTensor.Bridge.MulReal.logValue
      (
        Dt.d
          (fun s => (u s x).component j)
          t
      )

  exact
    hDt.d_log
      (fun s => (u s x).component j)
      t

/--
A compatible real spatial differential identifies the conventional negative
pressure gradient with the log of the intrinsic inverse pressure response.
-/
theorem realPressureForce_logField
    {T X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X PrimeTensor.MulReal dim)
    (t : T)
    (x : PrimeTensor.Point X dim)
    (j : PrimeTensor.Axis dim) :
    RealFluid.pressureForceComponent
        DR
        (logSpaceTimeScalarField p)
        t x j
      =
    -
      PrimeTensor.Bridge.MulReal.logValue
        (D.d j (p t) x) := by

  unfold RealFluid.pressureForceComponent
  unfold logSpaceTimeScalarField
  unfold logScalarField

  rw [
    hD.d_log j (p t) x
  ]

namespace PrimePairApprox

/--
Canonical multiplicative incompressibility conjugates exactly to additive real
divergence zero.
-/
theorem logProductIncompressible_to_real
    {T X : Type} {dim : Depth}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hD : SpatialLogCompatible D DR)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (h :
      PrimeTensor.MulFluid.Incompressible
        D u) :
    RealFluid.Incompressible
      DR
      (logSpaceTimeVectorField u) := by

  intro t x

  have hNative :=
    h t x

  have hLog :=
    congrArg
      PrimeTensor.Bridge.MulReal.logValue
      hNative

  rw [
    logValue_divergence,
    PrimeTensor.Bridge.MulReal.logValue_one
  ] at hLog

  exact
    (realDivergence_logField
      hD (u t) x).trans hLog

/--
The canonical completed multiplicative momentum balance conjugates exactly to
the normalized additive real momentum balance.
-/
theorem logProductMomentum_to_real
    {T X : Type} {dim : Depth}
    {Dt :
      PrimeTensor.TemporalDifferential
        T PrimeTensor.MulReal}
    {DtR :
      PrimeTensor.TemporalDifferential
        T ℝ}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (hDt :
      TemporalLogCompatible Dt DtR)
    (hD :
      SpatialLogCompatible D DR)
    (u :
      PrimeTensor.SpaceTimeVectorField
        T X PrimeTensor.MulReal dim)
    (p :
      PrimeTensor.SpaceTimeScalarField
        T X PrimeTensor.MulReal dim)
    (h :
      LogProductMomentumBalance
        Dt D u p) :
    RealFluid.MomentumBalance
      DtR DR
      (logSpaceTimeVectorField u)
      (logSpaceTimeScalarField p) := by

  intro t x j

  have hNative :=
    logProductMomentum_component
      Dt D u p h t x j

  have hLog :=
    congrArg
      PrimeTensor.Bridge.MulReal.logValue
      hNative

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_mul,
    logValue_logProductAdvectionFold,
    logValue_pressureForce_component,
    logValue_laplacianVector_component
  ] at hLog

  have hTime :=
    realTemporalDerivative_logField
      hDt u t x j

  have hAdv :=
    realAdvection_logField
      hD u t x j

  have hPressure :=
    realPressureForce_logField
      hD p t x j

  have hLap :=
    realLaplacianVector_logField
      hD u t x j

  calc
    (
      RealFluid.temporalVectorDerivative
        DtR
        (logSpaceTimeVectorField u)
        t x
    ).component j +
        (
          RealFluid.advection
            DR
            (logSpaceTimeVectorField u)
            t x
        ).component j
        =
      PrimeTensor.Bridge.MulReal.logValue
          (
            (Dt.vectorDerivative u t x).component j
          ) +
        PrimeTensor.Axis.fold (· + ·) dim
          (fun i =>
            PrimeTensor.Bridge.MulReal.logValue
                  ((u t x).component i) *
              PrimeTensor.Bridge.MulReal.logValue
                (
                  D.d i
                    (fun y => (u t y).component j)
                    x
                )) := by
          rw [hTime, hAdv]

    _ =
      -
          PrimeTensor.Bridge.MulReal.logValue
            (D.d j (p t) x) +
        PrimeTensor.Axis.fold (· + ·) dim
          (fun i =>
            PrimeTensor.Bridge.MulReal.logValue
              (
                D.d i
                  (
                    D.d i
                      (fun y => (u t y).component j)
                  )
                  x
              )) :=
      hLog

    _ =
      RealFluid.pressureForceComponent
          DR
          (logSpaceTimeScalarField p)
          t x j +
        (
          RealFluid.laplacianVector
            DR
            (logSpaceTimeVectorField u)
            t x
        ).component j := by
          rw [hPressure, hLap]

/--
A canonical multiplicative fluid solution therefore produces an additive real
solution whenever spatial and temporal derivative compatibility is supplied.
-/
noncomputable def LogProductSolution.toReal
    {T X : Type} {dim : Depth}
    {Dt :
      PrimeTensor.TemporalDifferential
        T PrimeTensor.MulReal}
    {DtR :
      PrimeTensor.TemporalDifferential
        T ℝ}
    {D :
      PrimeTensor.Differential
        X PrimeTensor.MulReal dim}
    {DR :
      PrimeTensor.Differential
        X ℝ dim}
    (s :
      LogProductSolution Dt D)
    (hDt :
      TemporalLogCompatible Dt DtR)
    (hD :
      SpatialLogCompatible D DR) :
    RealFluid.Solution DtR DR where

  velocity :=
    logSpaceTimeVectorField s.velocity

  pressure :=
    logSpaceTimeScalarField s.pressure

  incompressible :=
    logProductIncompressible_to_real
      hD
      s.velocity
      s.incompressible

  momentum :=
    logProductMomentum_to_real
      hDt hD
      s.velocity
      s.pressure
      s.momentum

end PrimePairApprox

end Bridge
end PrimeTensor
