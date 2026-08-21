import PrimeTensor.Bridge.Euclidean.Differential
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Classical regularity for the Euclidean 3D fluid bridge

`Euclidean.temporal` and `Euclidean.spatial3` are genuine conventional
derivative operators, but Mathlib's `deriv` is total.  Therefore a bare
`RealFluid.Solution Euclidean.temporal Euclidean.spatial3` does not by itself
assert that all derivatives appearing in the PDE exist classically.

This file adds that missing analytic layer.

For velocity we require:

* `C²` spatial regularity of every component at every fixed time;
* `C¹` temporal regularity of every component at every fixed point.

For pressure we require:

* `C¹` spatial regularity at every fixed time.

These hypotheses are enough to guarantee that every first temporal derivative,
first spatial derivative, pressure gradient derivative, and pure second
spatial derivative used by the incompressible Navier--Stokes equations is a
genuine derivative rather than a fallback value of the total `deriv`
operator.

The regularity predicate is then paired with the already-proved Euclidean real
fluid equations to define a concrete `ClassicalSolution3`.

Finally, a multiplicative log-product solution whose logged velocity and
pressure satisfy this regularity transports canonically to such a classical
real solution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

/--
`Axis d` is finite for every positive depth.  This instance is the missing
finite-coordinate witness needed for Mathlib's norm/topology on
`Point ℝ d = Axis d → ℝ`.
-/
instance axisFinite :
    (d : Depth) → Finite (PrimeTensor.Axis d)

  | .one => by

      let encode :
          PrimeTensor.Axis (.one) → PUnit :=
        fun _ => PUnit.unit

      apply
        Finite.of_injective encode

      intro a b h

      cases a
      cases b

      rfl

  | .succ d => by

      letI :
          Finite (PrimeTensor.Axis d) :=
        axisFinite d

      let encode :
          PrimeTensor.Axis (.succ d) →
            Option (PrimeTensor.Axis d)
        | .first => none
        | .next i => some i

      apply
        Finite.of_injective encode

      intro a b

      cases a <;> cases b <;> simp [encode]

noncomputable local instance axisFintype
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/--
A coordinate line through `x`, viewed as a smooth map from `ℝ` into Euclidean
coordinate space.
-/
theorem coordinateLine_contDiff
    {dim : Depth}
    (n : WithTop ℕ∞)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    ContDiff ℝ n
      (fun t : ℝ =>
        coordinateLine x i t) := by

  classical

  unfold coordinateLine

  exact
    contDiff_update n x i

/--
Replacing the same coordinate twice discards the intermediate replacement.
-/
@[simp]
theorem coordinateLine_coordinateLine
    {dim : Depth}
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim)
    (s t : ℝ) :
    coordinateLine
        (coordinateLine x i t)
        i s
      =
    coordinateLine x i s := by

  classical

  funext j

  by_cases hji : j = i

  · subst j
    simp [coordinateLine]

  · simp [coordinateLine, hji]

/--
Along one fixed coordinate line, the partial derivative field is the ordinary
one-variable derivative of the restricted scalar field.
-/
@[simp]
theorem partialDeriv_coordinateLine
    {dim : Depth}
    (f :
      PrimeTensor.ScalarField ℝ ℝ dim)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim)
    (t : ℝ) :
    partialDeriv i f
        (coordinateLine x i t)
      =
    deriv
      (
        fun s : ℝ =>
          f (coordinateLine x i s)
      )
      t := by

  unfold partialDeriv

  simp only [
    coordinateLine_coordinateLine,
    coordinateLine_same
  ]

/--
Standard spatial `C¹` regularity of a scalar field on the concrete Euclidean
coordinate space.
-/
def SpatialC1
    {dim : Depth}
    (f :
      PrimeTensor.ScalarField ℝ ℝ dim) :
    Prop :=
  ContDiff ℝ 1 f

/--
Standard spatial `C²` regularity of a scalar field on the concrete Euclidean
coordinate space.
-/
def SpatialC2
    {dim : Depth}
    (f :
      PrimeTensor.ScalarField ℝ ℝ dim) :
    Prop :=
  ContDiff ℝ 2 f

/--
Standard `C¹` regularity of a scalar function of real time.
-/
def TemporalC1
    (f : ℝ → ℝ) :
    Prop :=
  ContDiff ℝ 1 f

/--
Classical separated regularity needed by the three-dimensional incompressible
Navier--Stokes equation represented by this project.

Velocity is `C²` in space and `C¹` in time, componentwise. Pressure is `C¹`
in space.
-/
structure ClassicalRegularity3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    ) : Prop where

  velocity_spatial :
    ∀ (t : ℝ)
      (j : PrimeTensor.Axis Depth.three),
      SpatialC2
        (
          fun x =>
            (u t x).component j
        )

  velocity_temporal :
    ∀ (x : Point3)
      (j : PrimeTensor.Axis Depth.three),
      TemporalC1
        (
          fun t =>
            (u t x).component j
        )

  pressure_spatial :
    ∀ (t : ℝ),
      SpatialC1
        (p t)

/--
Under spatial `C¹` regularity, the first coordinate derivative used by
`spatial` is backed by an actual `HasDerivAt` witness.
-/
theorem SpatialC1.hasDerivAt_partial
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC1 f)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    HasDerivAt
      (
        fun t : ℝ =>
          f (coordinateLine x i t)
      )
      (
        (spatial dim).d i f x
      )
      (x i) := by

  have hLine :
      ContDiff ℝ 1
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
        ) := by

    exact
      hf.comp
        (
          coordinateLine_contDiff
            1 x i
        )

  have hDiff :
      DifferentiableAt ℝ
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
        )
        (x i) := by

    exact
      (
        hLine.differentiable_one
      ).differentiableAt

  change
    HasDerivAt
      (
        fun t : ℝ =>
          f (coordinateLine x i t)
      )
      (
        partialDeriv i f x
      )
      (x i)

  unfold partialDeriv

  exact
    hDiff.hasDerivAt

/--
Spatial `C²` regularity in particular supplies every genuine first coordinate
derivative.
-/
theorem SpatialC2.hasDerivAt_partial
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    HasDerivAt
      (
        fun t : ℝ =>
          f (coordinateLine x i t)
      )
      (
        (spatial dim).d i f x
      )
      (x i) := by

  apply
    SpatialC1.hasDerivAt_partial

  exact
    hf.of_le
      (by norm_num)

/--
Spatial `C²` regularity also supplies the genuine pure second coordinate
derivative used by the Laplacian.
-/
theorem SpatialC2.hasDerivAt_secondPartial
    {dim : Depth}
    {f :
      PrimeTensor.ScalarField ℝ ℝ dim}
    (hf : SpatialC2 f)
    (x : PrimeTensor.Point ℝ dim)
    (i : PrimeTensor.Axis dim) :
    HasDerivAt
      (
        fun t : ℝ =>
          (spatial dim).d i f
            (coordinateLine x i t)
      )
      (
        (spatial dim).d i
          ((spatial dim).d i f)
          x
      )
      (x i) := by

  have hLine :
      ContDiff ℝ 2
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
        ) := by

    exact
      hf.comp
        (
          coordinateLine_contDiff
            2 x i
        )

  have hDerivDiff :
      DifferentiableAt ℝ
        (
          deriv
            (
              fun t : ℝ =>
                f (coordinateLine x i t)
            )
        )
        (x i) := by

    exact
      (
        hLine.differentiable_deriv_two
      ).differentiableAt

  change
    HasDerivAt
      (
        fun t : ℝ =>
          partialDeriv i f
            (coordinateLine x i t)
      )
      (
        partialDeriv i
          (fun y =>
            partialDeriv i f y)
          x
      )
      (x i)

  have hInner :
      (
        fun t : ℝ =>
          partialDeriv i f
            (coordinateLine x i t)
      )
        =
      deriv
        (
          fun t : ℝ =>
            f (coordinateLine x i t)
        ) := by

    funext t

    exact
      partialDeriv_coordinateLine
        f x i t

  have hCoefficient :
      partialDeriv i
          (fun y =>
            partialDeriv i f y)
          x
        =
      deriv
        (
          deriv
            (
              fun t : ℝ =>
                f (coordinateLine x i t)
            )
        )
        (x i) := by

    change
      deriv
          (
            fun t : ℝ =>
              partialDeriv i f
                (coordinateLine x i t)
          )
          (x i)
        =
      deriv
          (
            deriv
              (
                fun t : ℝ =>
                  f (coordinateLine x i t)
              )
          )
          (x i)

    rw [hInner]

  rw [hCoefficient]

  rw [hInner]

  exact
    hDerivDiff.hasDerivAt

/--
Temporal `C¹` regularity guarantees that the concrete temporal differential is
a genuine derivative.
-/
theorem TemporalC1.hasDerivAt
    {f : ℝ → ℝ}
    (hf : TemporalC1 f)
    (t : ℝ) :
    HasDerivAt
      f
      (temporal.d f t)
      t := by

  have hDiff :
      DifferentiableAt ℝ f t := by

    exact
      (
        hf.differentiable_one
      ).differentiableAt

  change
    HasDerivAt
      f
      (deriv f t)
      t

  exact
    hDiff.hasDerivAt

/--
A real three-dimensional Euclidean fluid solution together with the standard
regularity ensuring that all derivatives in its PDE are classical.
-/
structure ClassicalSolution3 where

  solution :
    PrimeTensor.Bridge.RealFluid.Solution
      temporal
      spatial3

  regularity :
    ClassicalRegularity3
      solution.velocity
      solution.pressure

namespace ClassicalSolution3

/-- Classical velocity field. -/
def velocity
    (s : ClassicalSolution3) :
    PrimeTensor.SpaceTimeVectorField
      ℝ ℝ ℝ Depth.three :=
  s.solution.velocity

/-- Classical pressure field. -/
def pressure
    (s : ClassicalSolution3) :
    PrimeTensor.SpaceTimeScalarField
      ℝ ℝ ℝ Depth.three :=
  s.solution.pressure

theorem incompressible
    (s : ClassicalSolution3) :
    PrimeTensor.Bridge.RealFluid.Incompressible
      spatial3
      s.velocity :=
  s.solution.incompressible

theorem momentum
    (s : ClassicalSolution3) :
    PrimeTensor.Bridge.RealFluid.MomentumBalance
      temporal
      spatial3
      s.velocity
      s.pressure :=
  s.solution.momentum

end ClassicalSolution3

end Euclidean

namespace PrimePairApprox

/--
A multiplicative Euclidean 3D log-product solution together with classical
regularity of its logged real fields.
-/
structure ClassicalLogProductSolution3 where

  solution :
    LogProductSolution
      PrimeTensor.Bridge.Euclidean.mulTemporal
      PrimeTensor.Bridge.Euclidean.mulSpatial3

  regularity :
    PrimeTensor.Bridge.Euclidean.ClassicalRegularity3
      (
        PrimeTensor.Bridge.logSpaceTimeVectorField
          solution.velocity
      )
      (
        PrimeTensor.Bridge.logSpaceTimeScalarField
          solution.pressure
      )

namespace ClassicalLogProductSolution3

/--
A regular multiplicative Euclidean 3D solution canonically yields a classical
real three-dimensional incompressible fluid solution.
-/
noncomputable def toRealClassical
    (s : ClassicalLogProductSolution3) :
    PrimeTensor.Bridge.Euclidean.ClassicalSolution3 where

  solution :=
    s.solution.toRealEuclidean3

  regularity := by

    change
      PrimeTensor.Bridge.Euclidean.ClassicalRegularity3
        (
          PrimeTensor.Bridge.logSpaceTimeVectorField
            s.solution.velocity
        )
        (
          PrimeTensor.Bridge.logSpaceTimeScalarField
            s.solution.pressure
        )

    exact s.regularity

@[simp]
theorem toRealClassical_velocity
    (s : ClassicalLogProductSolution3) :
    s.toRealClassical.velocity =
      PrimeTensor.Bridge.logSpaceTimeVectorField
        s.solution.velocity := by
  rfl

@[simp]
theorem toRealClassical_pressure
    (s : ClassicalLogProductSolution3) :
    s.toRealClassical.pressure =
      PrimeTensor.Bridge.logSpaceTimeScalarField
        s.solution.pressure := by
  rfl

end ClassicalLogProductSolution3

end PrimePairApprox

end Bridge
end PrimeTensor
