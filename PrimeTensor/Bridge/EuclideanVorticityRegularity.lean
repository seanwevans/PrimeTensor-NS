import PrimeTensor.Bridge.EuclideanMixedPartials

/-!
# Regularity class for the classical vorticity equation

The explicit Navier--Stokes bridge currently packages the regularity needed to
interpret the velocity equation itself:

* velocity `C²` in space,
* velocity `C¹` in time,
* pressure `C¹` in space.

Taking the curl of that equation requires more.

1. `curl (Δu)` contains third spatial derivatives, so velocity must be `C³_x`.
2. `curl (∇p) = 0` uses second pressure derivatives, so pressure must be `C²_x`.
3. `∂t (curl u) = curl (∂t u)` requires time/space derivative commutation.

The first two are ordinary `ContDiff` assumptions.  The third is exposed
directly as the precise mixed spacetime condition needed by the curl argument.

This file deliberately does *not* derive the mixed time/space condition from a
joint spacetime regularity hypothesis yet.  Doing that cleanly is a separate
product-space calculus lemma.  Keeping it explicit prevents the vorticity
equation from silently assuming more regularity than the current classical
solution class provides.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

noncomputable local instance axisFintypeVorticityRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite
    (PrimeTensor.Axis d)

/-- Standard spatial `C³` regularity on the concrete Euclidean coordinate space. -/
def SpatialC3
    {dim : Depth}
    (f : PrimeTensor.ScalarField ℝ ℝ dim) :
    Prop :=
  ContDiff ℝ 3 f

/--
The additional regularity required to derive the classical three-dimensional
vorticity equation from an already classical Navier--Stokes solution.
-/
structure VorticityRegularity3
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

  /--
  Each velocity component is `C³` in space at every fixed time.  This is the
  extra spatial derivative needed to commute curl with the Laplacian.
  -/
  velocity_spatial_three :
    ∀ (t : ℝ)
      (j : PrimeTensor.Axis Depth.three),
      SpatialC3
        (
          fun x =>
            (u t x).component j
        )

  /--
  Pressure is `C²` in space at every fixed time.  This makes
  `curl (grad p) = 0` an ordinary Schwarz-symmetry consequence.
  -/
  pressure_spatial_two :
    ∀ (t : ℝ),
      SpatialC2
        (p t)

  /--
  The exact mixed spacetime derivative witness needed by the curl argument.

  This is deliberately stronger than merely asserting the equality

      ∂t ∂i u_j = ∂i ∂t u_j.

  Since the concrete temporal operator is Mathlib's total `deriv`, the curl
  proof needs a genuine `HasDerivAt` witness in order to use the linearity of
  differentiation through subtraction.
  -/
  velocity_space_time_hasDerivAt :
    ∀ (t : ℝ)
      (x : Point3)
      (i j : PrimeTensor.Axis Depth.three),

      HasDerivAt
        (
          fun τ =>
            spatial3.d
              i
              (
                fun y =>
                  (u τ y).component j
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
                      (u τ y).component j
                  )
                  t
            )
            x
        )
        t

/--
A classical Navier--Stokes solution equipped with exactly the extra regularity
needed for the classical vorticity equation.
-/
structure VorticitySolution3 where

  solution :
    ClassicalSolution3

  regularity :
    VorticityRegularity3
      solution.velocity
      solution.pressure

namespace VorticitySolution3

/-- Underlying classical velocity. -/
def velocity
    (s : VorticitySolution3) :
    PrimeTensor.SpaceTimeVectorField
      ℝ ℝ ℝ Depth.three :=
  s.solution.velocity

/-- Underlying classical pressure. -/
def pressure
    (s : VorticitySolution3) :
    PrimeTensor.SpaceTimeScalarField
      ℝ ℝ ℝ Depth.three :=
  s.solution.pressure

/-- The solution still satisfies the explicit normalized 3D Navier--Stokes PDE. -/
theorem isNavierStokes3
    (s : VorticitySolution3) :
    IsNavierStokes3
      s.velocity
      s.pressure := by

  exact
    s.solution.isNavierStokes3

/--
Pressure mixed spatial partials commute.  This is the exact cancellation used
by `curl (grad p) = 0`.
-/
theorem pressure_spatial_d_comm
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (i j : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (
          spatial3.d j
            (s.pressure t)
        )
        x
      =
    spatial3.d j
        (
          spatial3.d i
            (s.pressure t)
        )
        x := by

  exact
    (
      s.regularity.pressure_spatial_two t
    ).spatial_d_comm
      x i j

/--
The genuine mixed time/space derivative witness, exposed at solution level.
-/
theorem velocity_space_time_hasDerivAt
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (i j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (
        fun τ =>
          spatial3.d
            i
            (
              fun y =>
                (s.velocity τ y).component j
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
                    (s.velocity τ y).component j
                )
                t
          )
          x
      )
      t := by

  exact
    s.regularity.velocity_space_time_hasDerivAt
      t x i j

/--
The mixed time/space derivative values commute.  This is a consequence of the
stronger `HasDerivAt` witness above.
-/
theorem velocity_time_space_comm
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (i j : PrimeTensor.Axis Depth.three) :
    temporal.d
        (
          fun τ =>
            spatial3.d
              i
              (
                fun y =>
                  (s.velocity τ y).component j
              )
              x
        )
        t
      =
    spatial3.d
        i
        (
          fun y =>
            temporal.d
              (
                fun τ =>
                  (s.velocity τ y).component j
              )
              t
        )
        x := by

  unfold temporal

  exact
    (
      s.velocity_space_time_hasDerivAt
        t x i j
    ).deriv

/--
The original `C²_x` mixed-partial commutation remains available from the
underlying classical solution.
-/
theorem velocity_spatial_d_comm
    (s : VorticitySolution3)
    (t : ℝ)
    (x : Point3)
    (k i j : PrimeTensor.Axis Depth.three) :
    spatial3.d i
        (
          spatial3.d j
            (
              fun y =>
                (s.velocity t y).component k
            )
        )
        x
      =
    spatial3.d j
        (
          spatial3.d i
            (
              fun y =>
                (s.velocity t y).component k
            )
        )
        x := by

  exact
    s.solution.velocity_spatial_d_comm
      t x k i j

end VorticitySolution3

end Euclidean
end Bridge
end PrimeTensor
