import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.DiffusionWeak
import PrimeTensor.Fluid.Vorticity.Preterminal.Temporal.Separate

/-!
# Zeroth-order endpoint continuity: endpoint-independent old weak temporal RHS

The two spatial pieces of the old preterminal momentum equation are now
identified endpoint-independently against divergence-free compact tests:

* `Zero.DiffusionWeak`: the existing weak diffusion functional is the literal
  old physical Laplacian pairing;
* `Zero.ForcingWeak`: the canonical Leray-projected nonlinear weak pairing is
  the literal old physical advection pairing.

`Zero.WeakMomentum` already says that

    ∂ₜu + (u · ∇)u - Δu

has zero pairing against every divergence-free compact smooth test vector.

This file performs the remaining legal splitting of that residual.  At every
closed elapsed slice the compact-test products with

* the old temporal derivative,
* the old advection component,
* the old Laplacian component

are individually integrable.  Temporal integrability uses the already-proved
spatial continuity of the actual preterminal temporal derivative; the two
spatial terms use preterminal `C³_x` regularity.

Consequently

    weakTemporal
      =
    weakDiffusion - weakLerayForcing

on every closed elapsed slice, with no endpoint-continuity hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldWeakTemporal
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldWeakTemporal :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- In dimension three, the abstract `RealFluid.advection` component is the
explicit `realAdvectionComponent` used by the preterminal regularity layer. -/
theorem realFluid_advection_component_eq_realAdvectionComponent_zeroWeak
    (v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three)
    (s : ℝ)
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three) :
    (PrimeTensor.Bridge.RealFluid.advection
      spatial3 v s x).component j
      =
    realAdvectionComponent v s x j := by
  rw [realFluid_advection_component_eq_axisFold_three]
  unfold realAdvectionComponent
  rw [PrimeTensor.Bridge.Euclidean.axis_fold_three]

/-- Compact testing makes the old temporal derivative spatially integrable at
every closed elapsed slice. -/
theorem h3PreterminalLoggedVelocity_test_mul_temporalDerivative_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (φ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ))))
      (volume : Measure Point3) := by
  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  have hContinuous :
      Continuous
        (fun x : Point3 =>
          temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ))) :=
    loggedPreterminalTemporalDerivative_continuous_space
      hNS hAbs (h3AxisOfFin3 i)

  exact
    φ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hContinuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Compact testing makes the old physical advection component integrable at
every closed elapsed slice. -/
theorem h3PreterminalLoggedVelocity_test_mul_advection_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (φ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)))
      (volume : Measure Point3) := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  have hAdvC1 :
      SpatialC1
        (fun x : Point3 =>
          realAdvectionComponent
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x
            (h3AxisOfFin3 i)) :=
    hPDE.realAdvectionComponent_spatialC1
      hAbs (h3AxisOfFin3 i)

  have hEq :
      (fun x : Point3 =>
        (PrimeTensor.Bridge.RealFluid.advection
          spatial3
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i))
        =
      (fun x : Point3 =>
        realAdvectionComponent
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x
          (h3AxisOfFin3 i)) := by
    funext x

    exact
      realFluid_advection_component_eq_realAdvectionComponent_zeroWeak
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x
        (h3AxisOfFin3 i)

  have hIntegrandEq :
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)))
        =
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          (realAdvectionComponent
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x
            (h3AxisOfFin3 i))) := by
    funext x
    rw [congrFun hEq x]

  rw [hIntegrandEq]

  exact
    φ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hAdvC1.continuous.locallyIntegrable.locallyIntegrableOn Set.univ)

/-- Compact testing makes the old physical Laplacian component integrable at
every closed elapsed slice. -/
theorem h3PreterminalLoggedVelocity_test_mul_laplacianVector_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (φ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)))
      (volume : Measure Point3) := by
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  let hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T :=
    Classical.choose_spec hNS

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo ht hEnd q

  have hOldC3 :
      SpatialC3
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) := by
    unfold loggedVelocityComponent

    exact
      hPDE.regularity.velocity_spatial_three
        (t + (q : ℝ))
        hAbs
        (h3AxisOfFin3 i)

  have hOldC2 :
      SpatialC2
        (loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i)) :=
    hOldC3.of_le (by norm_num)

  have hD
      (k : Fin 3) :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x))
        (volume : Measure Point3) :=
    h3SpatialC2_test_mul_secondSpatialDerivative_integrable
      hOldC2
      (h3AxisOfFin3 k)
      φ

  have hSum :
      Integrable
        (fun x : Point3 =>
          ∑ k : Fin 3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ x)
              (spatial3.d
                (h3AxisOfFin3 k)
                (spatial3.d
                  (h3AxisOfFin3 k)
                  (loggedVelocityComponent
                    u
                    (t + (q : ℝ))
                    (h3AxisOfFin3 i)))
                x))
        (volume : Measure Point3) :=
    integrable_finsetSum
      (Finset.univ : Finset (Fin 3))
      (fun k _ => hD k)

  have hEq :
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i)))
        =
      (fun x : Point3 =>
        ∑ k : Fin 3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ x)
            (spatial3.d
              (h3AxisOfFin3 k)
              (spatial3.d
                (h3AxisOfFin3 k)
                (loggedVelocityComponent
                  u
                  (t + (q : ℝ))
                  (h3AxisOfFin3 i)))
              x)) := by
    funext x

    have hLap :=
      realFluid_laplacianVector_component_eq_fin_sum_three_endpoint
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x
        (h3AxisOfFin3 i)

    have hLoggedField :
        (fun y : Point3 =>
          (logSpaceTimeVectorField
            u
            (t + (q : ℝ))
            y).component
              (h3AxisOfFin3 i))
          =
        loggedVelocityComponent
          u
          (t + (q : ℝ))
          (h3AxisOfFin3 i) := by
      rfl

    have hLap' :
        (PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)
          =
        ∑ k : Fin 3,
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 i)))
            x := by
      rw [hLoggedField] at hLap
      exact hLap

    change
      (φ x) *
        (PrimeTensor.Bridge.RealFluid.laplacianVector
          spatial3
          (logSpaceTimeVectorField u)
          (t + (q : ℝ))
          x).component
            (h3AxisOfFin3 i)
        =
      ∑ k : Fin 3,
        (φ x) *
          spatial3.d
            (h3AxisOfFin3 k)
            (spatial3.d
              (h3AxisOfFin3 k)
              (loggedVelocityComponent
                u
                (t + (q : ℝ))
                (h3AxisOfFin3 i)))
            x

    rw [hLap', Finset.mul_sum]

  rw [hEq]

  exact hSum

/-- Endpoint-independent weak projected RHS pairing:
old weak diffusion minus canonical weak Leray forcing. -/
noncomputable def h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau) :
    ℝ :=
  h3PreterminalTailCanonicalWeakDiffusionPairingOnElapsed
      hNS ht hEnd hTail φ q
    -
  ∑ i : Fin 3,
    h3RawFinLerayOuterProductDivergenceWeakPairing
      (φ i) i
      (h3PreterminalTailCanonicalSpectralStateOnElapsed
        hNS ht hEnd hTail q)

/-- The old preterminal temporal derivative pairs exactly with the
endpoint-independent weak projected RHS on every closed elapsed slice. -/
theorem h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroWeakProjectedRHSPairingOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume)
      =
    h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed
      hNS ht hEnd hTail φ q := by
  let Tpair : Fin 3 → ℝ :=
    fun i =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        ∂volume

  let Apair : Fin 3 → ℝ :=
    fun i =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume

  let Dpair : Fin 3 → ℝ :=
    fun i =>
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))
        ∂volume

  have hWeak :=
    h3PreterminalLoggedVelocity_weakMomentumResidual_eq_zero
      hNS ht hEnd hTail q φ hφ

  have hSplit
      (i : Fin 3) :
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
              (fun a : ℝ =>
                loggedVelocityComponent
                  u a (h3AxisOfFin3 i) x)
              (t + (q : ℝ))
            +
           (PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)
            -
           (PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i))
        ∂volume)
        =
      Tpair i + Apair i - Dpair i := by
    let TF : Point3 → ℝ :=
      fun x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))

    let AF : Point3 → ℝ :=
      fun x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))

    let DF : Point3 → ℝ :=
      fun x =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          ((PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (logSpaceTimeVectorField u)
            (t + (q : ℝ))
            x).component
              (h3AxisOfFin3 i))

    have hTF :
        Integrable TF (volume : Measure Point3) := by
      dsimp only [TF]

      exact
        h3PreterminalLoggedVelocity_test_mul_temporalDerivative_integrable
          hNS ht hEnd hTail q i (φ i)

    have hAF :
        Integrable AF (volume : Measure Point3) := by
      dsimp only [AF]

      exact
        h3PreterminalLoggedVelocity_test_mul_advection_integrable
          hNS ht hEnd hTail q i (φ i)

    have hDF :
        Integrable DF (volume : Measure Point3) := by
      dsimp only [DF]

      exact
        h3PreterminalLoggedVelocity_test_mul_laplacianVector_integrable
          hNS ht hEnd hTail q i (φ i)

    calc
      (∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
              (fun a : ℝ =>
                loggedVelocityComponent
                  u a (h3AxisOfFin3 i) x)
              (t + (q : ℝ))
            +
           (PrimeTensor.Bridge.RealFluid.advection
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)
            -
           (PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i))
        ∂volume)
          =
        ∫ x : Point3,
          ((TF x + AF x) - DF x)
        ∂volume := by
          apply integral_congr_ae
          filter_upwards with x

          dsimp only [TF, AF, DF]

          rw [map_sub, map_add]
      _ =
        (∫ x : Point3, TF x ∂volume)
          +
        (∫ x : Point3, AF x ∂volume)
          -
        ∫ x : Point3, DF x ∂volume := by
          calc
            (∫ x : Point3, TF x + AF x - DF x ∂volume)
                =
              (∫ x : Point3, (TF + AF) x - DF x ∂volume) := by
                rfl
            _ =
              (∫ x : Point3, (TF + AF) x ∂volume)
                -
              ∫ x : Point3, DF x ∂volume := by
                exact integral_sub (hTF.add hAF) hDF
            _ =
              ((∫ x : Point3, TF x ∂volume)
                +
               (∫ x : Point3, AF x ∂volume))
                -
              ∫ x : Point3, DF x ∂volume := by
                have hAdd :
                    (∫ x : Point3, (TF + AF) x ∂volume)
                      =
                    (∫ x : Point3, TF x ∂volume)
                      +
                    ∫ x : Point3, AF x ∂volume := by
                  change
                    (∫ x : Point3, TF x + AF x ∂volume)
                      =
                    (∫ x : Point3, TF x ∂volume)
                      +
                    ∫ x : Point3, AF x ∂volume
                  exact integral_add hTF hAF

                exact
                  congrArg
                    (fun z : ℝ =>
                      z - ∫ x : Point3, DF x ∂volume)
                    hAdd
      _ =
        Tpair i + Apair i - Dpair i := by
          rfl

  have hResidual :
      (∑ i : Fin 3, Tpair i)
        +
      (∑ i : Fin 3, Apair i)
        -
      (∑ i : Fin 3, Dpair i)
        =
      0 := by
    calc
      (∑ i : Fin 3, Tpair i)
          +
        (∑ i : Fin 3, Apair i)
          -
        (∑ i : Fin 3, Dpair i)
          =
        ∑ i : Fin 3,
          (Tpair i + Apair i - Dpair i) := by
            rw [
              ← Finset.sum_add_distrib,
              ← Finset.sum_sub_distrib
            ]
      _ =
        ∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (temporal.d
                  (fun a : ℝ =>
                    loggedVelocityComponent
                      u a (h3AxisOfFin3 i) x)
                  (t + (q : ℝ))
                +
               (PrimeTensor.Bridge.RealFluid.advection
                  spatial3
                  (logSpaceTimeVectorField u)
                  (t + (q : ℝ))
                  x).component
                    (h3AxisOfFin3 i)
                -
               (PrimeTensor.Bridge.RealFluid.laplacianVector
                  spatial3
                  (logSpaceTimeVectorField u)
                  (t + (q : ℝ))
                  x).component
                    (h3AxisOfFin3 i))
            ∂volume := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hSplit i).symm
      _ = 0 :=
        hWeak

  have hForce :=
    h3PreterminalTailCanonicalZeroWeakForcingPairingOnElapsed_eq_oldAdvection
      hNS ht hEnd hTail q φ hφ

  have hDiff :=
    h3PreterminalTailCanonicalZeroWeakDiffusionPairingOnElapsed_eq_oldLaplacian
      hNS ht hEnd hTail q φ

  unfold
    h3PreterminalTailCanonicalZeroWeakProjectedRHSPairingOnElapsed

  dsimp only [Tpair, Apair, Dpair] at hResidual

  linarith

end

end Euclidean
end Bridge
end PrimeTensor
