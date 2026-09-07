import PrimeTensor.Fluid.Vorticity.Preterminal.Equation
import PrimeTensor.Fluid.Vorticity.Continuation.Frontier
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Separate continuity of the preterminal temporal derivative

The preterminal regularity package deliberately does not assume joint
spacetime continuity.

It does, however, contain enough information to prove the two sectionwise
continuity statements for the actual temporal derivative of the logged
velocity:

* for each fixed spatial point, `∂ₜu_j(t,x)` is continuous in time because
  `t ↦ u_j(t,x)` is `C¹` on `(0,T)`;
* for each fixed preterminal time, `∂ₜu_j(t,x)` is continuous in space because
  momentum rewrites it as

      Δu_j - (u · ∇)u_j - ∂_j p,

  whose three terms are spatially `C¹` under `C³_x` velocity and `C²_x`
  pressure.

Thus the remaining weak-FTC obstruction is genuinely a product-space issue:
separate continuity is available, but no invalid implication from separate to
joint continuity is made here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped Topology

noncomputable section

noncomputable local instance axisFintypePreterminalTemporalSeparate
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- At a fixed spatial point and velocity coordinate, the actual preterminal
temporal derivative is continuous in time at every strict preterminal time. -/
theorem loggedPreterminalTemporalDerivative_continuousAt_time
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    ContinuousAt
      (fun s : ℝ =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          s)
      t := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let f : ℝ → ℝ :=
    fun q : ℝ =>
      loggedVelocityComponent u q j x

  have hC1 :
      ContDiffOn
        ℝ 1
        f
        (Set.Ioo (0 : ℝ) T) := by
    dsimp only [f]
    simpa only [loggedVelocityComponent] using
      hPDE.regularity.velocity_temporal_one x j

  have hCriterion :
      ContDiffOn
          ℝ 1
          f
          (Set.Ioo (0 : ℝ) T)
        ↔
      DifferentiableOn
          ℝ
          f
          (Set.Ioo (0 : ℝ) T)
        ∧
      ContinuousOn
          (deriv f)
          (Set.Ioo (0 : ℝ) T) := by
    simpa using
      (contDiffOn_succ_iff_deriv_of_isOpen
        (𝕜 := ℝ)
        (f := f)
        (s := Set.Ioo (0 : ℝ) T)
        (n := 0)
        isOpen_Ioo)

  have hDerivContinuous :
      ContinuousOn
        (deriv f)
        (Set.Ioo (0 : ℝ) T) :=
    (hCriterion.1 hC1).2

  have hWithin :
      ContinuousWithinAt
        (deriv f)
        (Set.Ioo (0 : ℝ) T)
        t :=
    hDerivContinuous t ht

  have hAt :
      ContinuousAt
        (deriv f)
        t :=
    hWithin.continuousAt
      (isOpen_Ioo.mem_nhds ht)

  simpa only [temporal_d, f] using hAt

/-- At a fixed strict preterminal time, one actual temporal-derivative
coordinate is continuous as a function of space. -/
theorem loggedPreterminalTemporalDerivative_continuous_space
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          t) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  let uj : ScalarField3 :=
    loggedVelocityComponent u t j

  have huj3 :
      SpatialC3 uj := by
    dsimp only [uj, loggedVelocityComponent]
    exact
      hPDE.regularity.velocity_spatial_three
        t ht j

  have hLaplacian :
      SpatialC1
        (PrimeTensor.Bridge.RealFluid.laplacian
          spatial3 uj) :=
    PrimeTensor.Bridge.Euclidean.SpatialC3.laplacian3_spatialC1
      huj3

  have hAdvection :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            t x j) :=
    hPDE.realAdvectionComponent_spatialC1
      ht j

  have hp2 :
      SpatialC2 (p t) :=
    hPDE.regularity.pressure_spatial_two
      t ht

  have hPressure :
      SpatialC1
        (spatial3.d j (p t)) :=
    PrimeTensor.Bridge.Euclidean.SpatialC2.partialDeriv_contDiff_one
      hp2 j

  have hRHS :
      SpatialC1
        (fun x : Point3 =>
          PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj x
            -
          realAdvectionComponent
              (logSpaceTimeVectorField u)
              t x j
            -
          spatial3.d j (p t) x) :=
    (hLaplacian.sub hAdvection).sub hPressure

  have hEq :
      (fun x : Point3 =>
        temporal.d
          (fun q : ℝ =>
            loggedVelocityComponent u q j x)
          t)
        =
      (fun x : Point3 =>
        PrimeTensor.Bridge.RealFluid.laplacian
              spatial3 uj x
            -
        realAdvectionComponent
              (logSpaceTimeVectorField u)
              t x j
            -
        spatial3.d j (p t) x) := by
    funext x

    have hMomentum :=
      hPDE.temporalComponent_eq_laplacian_sub_advection_sub_pressure
        ht x j

    change
      temporal.d
          (fun q : ℝ =>
            (logSpaceTimeVectorField u q x).component j)
          t
        =
      PrimeTensor.Bridge.RealFluid.laplacian
          spatial3
          (fun y : Point3 =>
            (logSpaceTimeVectorField u t y).component j)
          x
        -
      realAdvectionComponent
          (logSpaceTimeVectorField u)
          t x j
        -
      spatial3.d j (p t) x

    exact hMomentum

  rw [hEq]

  exact hRHS.continuous

/-- The actual temporal derivative of every logged velocity coordinate is
separately continuous on the open preterminal cylinder. -/
theorem loggedPreterminalTemporalDerivative_separatelyContinuous
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T) :
    (∀
      (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
      ∀ j : PrimeTensor.Axis Depth.three,
        Continuous
          (fun x : Point3 =>
            temporal.d
              (fun q : ℝ =>
                loggedVelocityComponent u q j x)
              t))
      ∧
    (∀
      (x : Point3)
      (j : PrimeTensor.Axis Depth.three)
      (t : ℝ),
      t ∈ Set.Ioo (0 : ℝ) T →
        ContinuousAt
          (fun s : ℝ =>
            temporal.d
              (fun q : ℝ =>
                loggedVelocityComponent u q j x)
              s)
          t) := by
  constructor
  · intro t ht j
    exact
      loggedPreterminalTemporalDerivative_continuous_space
        hNS ht j
  · intro x j t ht
    exact
      loggedPreterminalTemporalDerivative_continuousAt_time
        hNS ht x j

end

end Euclidean
end Bridge
end PrimeTensor
