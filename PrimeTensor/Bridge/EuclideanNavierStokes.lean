import PrimeTensor.Bridge.EuclideanClassical

/-!
# Explicit three-dimensional Navier--Stokes equations

The Euclidean bridge has now supplied:

* real time `t : ℝ`;
* Euclidean space `Point3 = Axis Depth.three → ℝ`;
* ordinary coordinate derivatives;
* `C¹_t / C²_x` velocity regularity and `C¹_x` pressure regularity;
* incompressibility and normalized momentum balance.

This file performs the final notational identification.  It expands the
three-axis folds into the familiar `x/y/z` component equations.

Thus no abstract `Axis.fold`, `RealFluid.advection`, or `RealFluid.laplacian`
remains in the displayed PDE:

    ∂x u_x + ∂y u_y + ∂z u_z = 0

and, for each component `j`,

    ∂t u_j
      + u_x ∂x u_j
      + u_y ∂y u_j
      + u_z ∂z u_j
    =
      - ∂j p
      + ∂xx u_j
      + ∂yy u_j
      + ∂zz u_j.

The association of additions follows Lean's syntax, but this is exactly the
normalized density-one, viscosity-one incompressible 3D Navier--Stokes system.

The final theorem transports a regular multiplicative log-product solution
directly to this explicit real PDE.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

namespace ClassicalSolution3

/--
The incompressibility equation expanded into the three conventional coordinate
directions.
-/
theorem incompressible_xyz
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3) :
    spatial3.d
          xAxis
          (fun y =>
            (s.velocity t y).component xAxis)
          x
      +
        (
          spatial3.d
              yAxis
              (fun y =>
                (s.velocity t y).component yAxis)
              x
          +
          spatial3.d
              zAxis
              (fun y =>
                (s.velocity t y).component zAxis)
              x
        )
      =
    0 := by

  have h :=
    s.solution.incompressible t x

  unfold
    PrimeTensor.Bridge.RealFluid.Incompressible
    PrimeTensor.Bridge.RealFluid.divergence
    at h

  rw [
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ] at h

  simpa [
    PrimeTensor.Bridge.Euclidean.ClassicalSolution3.velocity
  ] using h

/--
The normalized momentum equation expanded into ordinary `x/y/z` components.
-/
theorem momentum_xyz
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    temporal.d
          (fun τ =>
            (s.velocity τ x).component j)
          t
      +
        (
          (s.velocity t x).component xAxis *
              spatial3.d
                xAxis
                (fun y =>
                  (s.velocity t y).component j)
                x
          +
          (
            (s.velocity t x).component yAxis *
                spatial3.d
                  yAxis
                  (fun y =>
                    (s.velocity t y).component j)
                  x
            +
            (s.velocity t x).component zAxis *
                spatial3.d
                  zAxis
                  (fun y =>
                    (s.velocity t y).component j)
                  x
          )
        )
      =
    -
        spatial3.d
          j
          (s.pressure t)
          x
      +
        (
          spatial3.d
              xAxis
              (
                spatial3.d
                  xAxis
                  (fun y =>
                    (s.velocity t y).component j)
              )
              x
          +
          (
            spatial3.d
                yAxis
                (
                  spatial3.d
                    yAxis
                    (fun y =>
                      (s.velocity t y).component j)
                )
                x
            +
            spatial3.d
                zAxis
                (
                  spatial3.d
                    zAxis
                    (fun y =>
                      (s.velocity t y).component j)
                )
                x
          )
        ) := by

  have h :=
    s.solution.momentum t x j

  change
    temporal.d
          (fun τ =>
            (s.solution.velocity τ x).component j)
          t
      +
        PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun i =>
            (s.solution.velocity t x).component i *
              spatial3.d
                i
                (fun y =>
                  (s.solution.velocity t y).component j)
                x)
      =
    -
        spatial3.d
          j
          (s.solution.pressure t)
          x
      +
        PrimeTensor.Axis.fold
          (· + ·)
          Depth.three
          (fun i =>
            spatial3.d
              i
              (
                spatial3.d
                  i
                  (fun y =>
                    (s.solution.velocity t y).component j)
              )
              x)
    at h

  rw [
    PrimeTensor.Bridge.Euclidean.axis_fold_three,
    PrimeTensor.Bridge.Euclidean.axis_fold_three
  ] at h

  simpa [
    PrimeTensor.Bridge.Euclidean.ClassicalSolution3.velocity,
    PrimeTensor.Bridge.Euclidean.ClassicalSolution3.pressure
  ] using h

/--
All derivative values appearing in the explicit velocity equation are genuine
classical derivatives, supplied by the regularity witness.
-/
theorem velocity_time_hasDerivAt
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun τ =>
        (s.velocity τ x).component j)
      (
        temporal.d
          (fun τ =>
            (s.velocity τ x).component j)
          t
      )
      t := by

  exact
    s.regularity.velocity_temporal x j
      |>.hasDerivAt t

/--
Every first spatial velocity derivative in the explicit PDE is genuine.
-/
theorem velocity_space_hasDerivAt
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (i j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (
        fun r : ℝ =>
          (s.velocity t
            (coordinateLine x i r)).component j
      )
      (
        spatial3.d
          i
          (fun y =>
            (s.velocity t y).component j)
          x
      )
      (x i) := by

  exact
    s.regularity.velocity_spatial t j
      |>.hasDerivAt_partial x i

/--
Every pure second spatial velocity derivative in the Laplacian is genuine.
-/
theorem velocity_secondSpace_hasDerivAt
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (i j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (
        fun r : ℝ =>
          spatial3.d
            i
            (fun y =>
              (s.velocity t y).component j)
            (coordinateLine x i r)
      )
      (
        spatial3.d
          i
          (
            spatial3.d
              i
              (fun y =>
                (s.velocity t y).component j)
          )
          x
      )
      (x i) := by

  exact
    s.regularity.velocity_spatial t j
      |>.hasDerivAt_secondPartial x i

/--
Every pressure-gradient derivative in the explicit PDE is genuine.
-/
theorem pressure_space_hasDerivAt
    (s : ClassicalSolution3)
    (t : ℝ)
    (x : Point3)
    (i : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (
        fun r : ℝ =>
          s.pressure t
            (coordinateLine x i r)
      )
      (
        spatial3.d
          i
          (s.pressure t)
          x
      )
      (x i) := by

  exact
    s.regularity.pressure_spatial t
      |>.hasDerivAt_partial x i

end ClassicalSolution3

/--
Explicit componentwise normalized incompressible Navier--Stokes predicate in
the concrete three-dimensional Euclidean model.
-/
def IsNavierStokes3
    (
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ ℝ Depth.three
    )
    (
      p :
        PrimeTensor.SpaceTimeScalarField
          ℝ ℝ ℝ Depth.three
    ) : Prop :=

  ClassicalRegularity3 u p
    ∧

  (
    ∀ (t : ℝ) (x : Point3),

      spatial3.d
            xAxis
            (fun y =>
              (u t y).component xAxis)
            x
        +
          (
            spatial3.d
                yAxis
                (fun y =>
                  (u t y).component yAxis)
                x
            +
            spatial3.d
                zAxis
                (fun y =>
                  (u t y).component zAxis)
                x
          )
        =
      0
  )
    ∧

  (
    ∀ (t : ℝ)
      (x : Point3)
      (j : PrimeTensor.Axis Depth.three),

      temporal.d
            (fun τ =>
              (u τ x).component j)
            t
        +
          (
            (u t x).component xAxis *
                spatial3.d
                  xAxis
                  (fun y =>
                    (u t y).component j)
                  x
            +
            (
              (u t x).component yAxis *
                  spatial3.d
                    yAxis
                    (fun y =>
                      (u t y).component j)
                    x
              +
              (u t x).component zAxis *
                  spatial3.d
                    zAxis
                    (fun y =>
                      (u t y).component j)
                    x
            )
          )
        =
      -
          spatial3.d
            j
            (p t)
            x
        +
          (
            spatial3.d
                xAxis
                (
                  spatial3.d
                    xAxis
                    (fun y =>
                      (u t y).component j)
                )
                x
            +
            (
              spatial3.d
                  yAxis
                  (
                    spatial3.d
                      yAxis
                      (fun y =>
                        (u t y).component j)
                  )
                  x
              +
              spatial3.d
                  zAxis
                  (
                    spatial3.d
                      zAxis
                      (fun y =>
                        (u t y).component j)
                  )
                  x
            )
          )
  )

/--
Every `ClassicalSolution3` satisfies the explicit ordinary normalized
three-dimensional incompressible Navier--Stokes predicate.
-/
theorem ClassicalSolution3.isNavierStokes3
    (s : ClassicalSolution3) :
    IsNavierStokes3
      s.velocity
      s.pressure := by

  refine
    ⟨
      s.regularity,
      ?_,
      ?_
    ⟩

  · exact
      s.incompressible_xyz

  · exact
      s.momentum_xyz

end Euclidean

namespace PrimePairApprox
namespace ClassicalLogProductSolution3

/--
A regular multiplicative three-dimensional Euclidean log-product solution
satisfies the explicit conventional normalized incompressible Navier--Stokes
system after logarithmic conjugation.
-/
theorem toRealClassical_isNavierStokes3
    (s :
      PrimeTensor.Bridge.PrimePairApprox.ClassicalLogProductSolution3) :
    PrimeTensor.Bridge.Euclidean.IsNavierStokes3
      s.toRealClassical.velocity
      s.toRealClassical.pressure :=

  s.toRealClassical.isNavierStokes3

end ClassicalLogProductSolution3
end PrimePairApprox

end Bridge
end PrimeTensor
