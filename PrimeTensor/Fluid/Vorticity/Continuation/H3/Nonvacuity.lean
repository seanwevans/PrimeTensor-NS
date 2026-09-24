import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Selected.Old.H3.Path.Admissible
import PrimeTensor.Fluid.Vorticity.Continuation.Restart

/-!
# Non-vacuity of the preterminal H³ path class

The continuation architecture is stated for

    LoggedPreterminalH3PathAdmissible u T.

Universal implications over that class are mathematically meaningful only once
the class is known to have an inhabitant.

This file supplies an explicit sanity witness.  Start from the ordinary real
zero velocity and zero pressure on the preterminal interval `(0,1)`.  They
satisfy the normalized real Navier--Stokes equations identically.  Lift the
real velocity through `nativeSpaceTimeVectorFieldOfReal`.  Its logarithmic
coordinates are again the real zero field, so every spatial derivative through
order three is zero, every squared H³ density is integrable, and the normalized
canonical H³ energy is the constant function `1`.

Consequently:

* `LoggedPreterminalH3PathAdmissible` is inhabited;
* the already-closed path-to-energy-class theorem has a concrete input;
* `PreterminalH3EnergyClass` is therefore inhabited as well.

This is only a non-vacuity/regression theorem.  It contributes no estimate
toward the global continuation problem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3Nonvacuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

private noncomputable def h3NonvacuityZeroRealVelocity :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  fun _ _ =>
    ⟨fun _ => 0⟩

private noncomputable def h3NonvacuityZeroRealPressure :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  fun _ _ => 0

private noncomputable def h3NonvacuityZeroNativeVelocity :
    SpaceTimeVectorField ℝ ℝ MulReal Depth.three :=
  nativeSpaceTimeVectorFieldOfReal
    h3NonvacuityZeroRealVelocity

private theorem h3Nonvacuity_spatial_d_zero
    (i : PrimeTensor.Axis Depth.three) :
    spatial3.d i (fun _ : Point3 => (0 : ℝ))
      =
    (fun _ : Point3 => (0 : ℝ)) := by

  funext x

  exact
    spatial_d_eq_of_hasDerivAt
      (hasDerivAt_const (x i) 0)

private theorem h3Nonvacuity_temporal_d_zero
    (t : ℝ) :
    temporal.d (fun _ : ℝ => (0 : ℝ)) t = 0 := by

  exact
    temporal_d_eq_of_hasDerivAt
      (hasDerivAt_const t 0)

/-- The ordinary real zero velocity and zero pressure solve preterminal
Navier--Stokes on `(0,1)`. -/
private theorem h3Nonvacuity_zeroReal_preterminalNavierStokes :
    PreterminalNavierStokes3
      h3NonvacuityZeroRealVelocity
      h3NonvacuityZeroRealPressure
      1 := by

  refine
    {
      positive_terminal := by norm_num
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

      unfold SpatialC3

      simpa [h3NonvacuityZeroRealVelocity] using
        (contDiff_const :
          ContDiff ℝ 3 (fun _ : Point3 => (0 : ℝ)))

    · intro x j

      simpa [h3NonvacuityZeroRealVelocity] using
        (contDiffOn_const :
          ContDiffOn ℝ 1
            (fun _ : ℝ => (0 : ℝ))
            (Set.Ioo (0 : ℝ) 1))

    · intro t ht

      unfold SpatialC2

      change
        ContDiff ℝ 2
          (fun _ : Point3 => (0 : ℝ))

      exact contDiff_const

    · intro t ht x i j

      have hSpatial :
          spatial3.d
              i
              (fun _ : Point3 => (0 : ℝ))
            =
          (fun _ : Point3 => (0 : ℝ)) :=
        h3Nonvacuity_spatial_d_zero i

      have hTime :
          temporal.d
              (fun _ : ℝ => (0 : ℝ))
              t
            =
          0 :=
        h3Nonvacuity_temporal_d_zero t

      rw [show
        (fun τ : ℝ =>
          spatial3.d
            i
            (fun y : Point3 =>
              (h3NonvacuityZeroRealVelocity τ y).component j)
            x)
          =
        (fun _ : ℝ => (0 : ℝ)) by
          funext τ
          simpa [h3NonvacuityZeroRealVelocity] using
            congrFun hSpatial x
      ]

      rw [show
        spatial3.d
            i
            (fun y : Point3 =>
              temporal.d
                (fun τ : ℝ =>
                  (h3NonvacuityZeroRealVelocity τ y).component j)
                t)
            x
          =
        0 by
          have hField :
              (fun y : Point3 =>
                temporal.d
                  (fun τ : ℝ =>
                    (h3NonvacuityZeroRealVelocity τ y).component j)
                  t)
                =
              (fun _ : Point3 => (0 : ℝ)) := by
            funext y
            simpa [h3NonvacuityZeroRealVelocity] using hTime

          rw [hField]
          exact congrFun hSpatial x
      ]

      exact
        hasDerivAt_const t 0

  · intro t ht x

    unfold PrimeTensor.Bridge.RealFluid.divergence

    rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]

    simp only [h3NonvacuityZeroRealVelocity]

    rw [
      congrFun (h3Nonvacuity_spatial_d_zero xAxis) x,
      congrFun (h3Nonvacuity_spatial_d_zero yAxis) x,
      congrFun (h3Nonvacuity_spatial_d_zero zAxis) x
    ]

    norm_num

  · intro t ht x j

    have hSpace :
        ∀ i : PrimeTensor.Axis Depth.three,
          spatial3.d i (fun _ : Point3 => (0 : ℝ))
            =
          (fun _ : Point3 => (0 : ℝ)) :=
      fun i => h3Nonvacuity_spatial_d_zero i

    have hTime :
        temporal.d (fun _ : ℝ => (0 : ℝ)) t = 0 :=
      h3Nonvacuity_temporal_d_zero t

    have hPressure :
        spatial3.d
            j
            (h3NonvacuityZeroRealPressure t)
            x
          =
        0 := by
      change
        spatial3.d
            j
            (fun _ : Point3 => (0 : ℝ))
            x
          =
        0

      exact
        congrFun
          (hSpace j)
          x

    unfold
      PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
      PrimeTensor.Bridge.RealFluid.advection
      PrimeTensor.Bridge.RealFluid.pressureForceComponent
      PrimeTensor.Bridge.RealFluid.laplacianVector
      PrimeTensor.Bridge.RealFluid.laplacian

    simp only [
      h3NonvacuityZeroRealVelocity
    ]

    rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]
    rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]

    simp only [
      hTime,
      hSpace xAxis,
      hSpace yAxis,
      hSpace zAxis
    ]

    rw [hPressure]

    norm_num

/-- The zero real preterminal solution lifts to a logged-native admissible
preterminal velocity. -/
private theorem h3Nonvacuity_zeroNative_loggedAdmissible :
    LoggedPreterminalNavierStokesAdmissible
      h3NonvacuityZeroNativeVelocity
      1 := by

  exact
    loggedPreterminalNavierStokesAdmissible_nativeSpaceTimeVectorFieldOfReal
      h3Nonvacuity_zeroReal_preterminalNavierStokes

private theorem h3Nonvacuity_loggedVelocityComponent_eq_zero
    (t : ℝ)
    (j : PrimeTensor.Axis Depth.three) :
    loggedVelocityComponent
        h3NonvacuityZeroNativeVelocity
        t j
      =
    (fun _ : Point3 => (0 : ℝ)) := by

  funext x

  simp [
    loggedVelocityComponent,
    h3NonvacuityZeroNativeVelocity,
    h3NonvacuityZeroRealVelocity
  ]

/-- Every H³ slot of the lifted zero field is square-integrable. -/
private theorem h3Nonvacuity_zeroNative_velocityH3IntegrableAt
    (t : ℝ) :
    VelocityH3IntegrableAt
      h3NonvacuityZeroNativeVelocity
      t := by

  intro j

  have h0 :
      loggedVelocityComponent
          h3NonvacuityZeroNativeVelocity
          t j
        =
      (fun _ : Point3 => (0 : ℝ)) :=
    h3Nonvacuity_loggedVelocityComponent_eq_zero t j

  have hd
      (i : PrimeTensor.Axis Depth.three) :
      spatial3.d
          i
          (loggedVelocityComponent
            h3NonvacuityZeroNativeVelocity t j)
        =
      (fun _ : Point3 => (0 : ℝ)) := by
    rw [h0]
    exact h3Nonvacuity_spatial_d_zero i

  unfold SpatialL2SquareIntegrable

  constructor

  · rw [h0]
    simpa using
      (MeasureTheory.integrable_zero :
        MeasureTheory.Integrable
          (fun _ : Point3 => (0 : ℝ)))

  · constructor

    · intro i
      rw [hd i]
      simpa using
        (MeasureTheory.integrable_zero :
          MeasureTheory.Integrable
            (fun _ : Point3 => (0 : ℝ)))

    · constructor

      · intro i k
        rw [hd k]
        rw [h3Nonvacuity_spatial_d_zero i]
        simpa using
          (MeasureTheory.integrable_zero :
            MeasureTheory.Integrable
              (fun _ : Point3 => (0 : ℝ)))

      · intro i k l
        rw [hd l]
        rw [h3Nonvacuity_spatial_d_zero k]
        rw [h3Nonvacuity_spatial_d_zero i]
        simpa using
          (MeasureTheory.integrable_zero :
            MeasureTheory.Integrable
              (fun _ : Point3 => (0 : ℝ)))

/-- The normalized canonical H³ energy of the lifted zero solution is exactly
one at every time. -/
private theorem h3Nonvacuity_zeroNative_velocityH3EnergyAt_eq_one
    (t : ℝ) :
    velocityH3EnergyAt
        h3NonvacuityZeroNativeVelocity
        t
      =
    1 := by

  have h0 :
      ∀ j : PrimeTensor.Axis Depth.three,
        loggedVelocityComponent
            h3NonvacuityZeroNativeVelocity
            t j
          =
        (fun _ : Point3 => (0 : ℝ)) :=
    h3Nonvacuity_loggedVelocityComponent_eq_zero t

  have hd
      (i : PrimeTensor.Axis Depth.three) :
      spatial3.d i (fun _ : Point3 => (0 : ℝ))
        =
      (fun _ : Point3 => (0 : ℝ)) :=
    h3Nonvacuity_spatial_d_zero i

  unfold
    velocityH3EnergyAt
    velocityH3Energy0At
    velocityH3Energy1At
    velocityH3Energy2At
    velocityH3Energy3At
    spatialSquareEnergy

  simp [
    h0,
    hd
  ]

/-- The lifted zero solution is a concrete inhabitant of the strong H³
preterminal path class. -/
theorem h3Nonvacuity_zeroNative_h3PathAdmissible :
    LoggedPreterminalH3PathAdmissible
      h3NonvacuityZeroNativeVelocity
      1 := by

  refine
    {
      navier_stokes :=
        h3Nonvacuity_zeroNative_loggedAdmissible
      velocity_h3_integrable := ?_
      energy_continuousAt := ?_
    }

  · intro s hs
    exact
      h3Nonvacuity_zeroNative_velocityH3IntegrableAt s

  · intro s hs

    have hEnergy :
        velocityH3EnergyAt
            h3NonvacuityZeroNativeVelocity
          =
        (fun _ : ℝ => (1 : ℝ)) := by
      funext t
      exact
        h3Nonvacuity_zeroNative_velocityH3EnergyAt_eq_one t

    rw [hEnergy]

    exact continuousAt_const

/-- Explicit non-vacuity of the H³-path admissibility predicate. -/
theorem exists_loggedPreterminalH3PathAdmissible :
    ∃
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T : ℝ),
        LoggedPreterminalH3PathAdmissible u T := by

  exact
    ⟨
      h3NonvacuityZeroNativeVelocity,
      1,
      h3Nonvacuity_zeroNative_h3PathAdmissible
    ⟩

/-- The already-closed path-to-energy-class theorem therefore also has an
actual concrete input: the high-order energy class is non-vacuous. -/
theorem exists_loggedPreterminalH3PathAdmissible_and_energyClass :
    ∃
      (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
      (T a : ℝ),
        LoggedPreterminalH3PathAdmissible u T
          ∧
        PreterminalH3EnergyClass u a T := by

  obtain
    ⟨a, hClass⟩ :=
    h3Preterminal_energyClass_of_h3PathAdmissible
      h3Nonvacuity_zeroNative_h3PathAdmissible

  exact
    ⟨
      h3NonvacuityZeroNativeVelocity,
      1,
      a,
      h3Nonvacuity_zeroNative_h3PathAdmissible,
      hClass
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
