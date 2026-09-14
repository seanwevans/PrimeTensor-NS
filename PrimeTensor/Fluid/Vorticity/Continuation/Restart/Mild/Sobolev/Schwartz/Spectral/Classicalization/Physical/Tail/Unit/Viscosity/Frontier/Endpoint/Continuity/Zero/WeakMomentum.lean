import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.PointwiseFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Pressure.Classical.Bridge

/-!
# Zeroth-order endpoint continuity: endpoint-independent old weak momentum

`Zero.PointwiseFTC` gives scalar FTC directly on the old preterminal branch,
without assuming endpoint continuity.  The next seam is pressure elimination.

For every preterminal elapsed slice and every compactly supported smooth
divergence-free test vector `φ`, the old classical momentum equation gives

    ∂ₜu + (u · ∇)u - Δu = -∇p.

The pressure slice is spatially `C²`, hence `C¹`.  The generic distributional
integration-by-parts theorem already in PrimeTensor therefore annihilates the
pressure gradient against `φ`.

PrimeTensor already contains the generic theorem saying that any spatially
`C¹` scalar gradient has zero classical pairing against an H³ weak
divergence-free test vector.  This file reuses that theorem to show that the
old preterminal velocity satisfies the pressure-free weak momentum identity on
every closed elapsed slice.

No endpoint reconstructed path, selected restart, Fourier time continuity, or
Banach-valued temporal derivative is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldWeakMomentum
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldWeakMomentum :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At every old preterminal elapsed slice, the pressure-free momentum residual

    ∂ₜu + (u · ∇)u - Δu

has zero pairing against every compactly supported smooth divergence-free test
vector.

This statement is entirely on the old branch. -/
theorem h3PreterminalLoggedVelocity_weakMomentumResidual_eq_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (_hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ) :
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
        ∂volume
      =
    0 := by
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
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hPressureC2 :
      SpatialC2 (pOld (t + (q : ℝ))) :=
    hPDE.regularity.pressure_spatial_two
      (t + (q : ℝ)) hAbs

  have hPressureC1 :
      SpatialC1 (pOld (t + (q : ℝ))) := by
    exact hPressureC2.of_le (by norm_num)

  have hPressure :
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pOld (t + (q : ℝ)))
              x)
          ∂volume
        =
      0 :=
    h3SpatialC1_gradient_pairing_eq_zero_of_testDivergenceFree
      (pOld (t + (q : ℝ)))
      hPressureC1
      φ
      hφ

  have hResidual
      (i : Fin 3)
      (x : Point3) :
      temporal.d
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
          (h3AxisOfFin3 i)
        =
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x := by
    have hMomentum :=
      hPDE.momentum
        (t + (q : ℝ))
        hAbs
        x
        (h3AxisOfFin3 i)

    change
      temporal.d
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
        =
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x
        +
      (PrimeTensor.Bridge.RealFluid.laplacianVector
        spatial3
        (logSpaceTimeVectorField u)
        (t + (q : ℝ))
        x).component
          (h3AxisOfFin3 i)
      at hMomentum

    linarith

  calc
    (∑ i : Fin 3,
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
        ∂volume)
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          -
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pOld (t + (q : ℝ)))
              x)
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      apply integral_congr_ae
      exact
        Filter.Eventually.of_forall
          (fun x => by
            change
              (φ i x) *
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
                =
              -
              ((φ i x) *
                spatial3.d
                  (h3AxisOfFin3 i)
                  (pOld (t + (q : ℝ)))
                  x)
            rw [hResidual i x]
            ring)
    _ =
      -
      (∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pOld (t + (q : ℝ)))
              x)
          ∂volume) := by
      simp_rw [integral_neg]
      rw [Finset.sum_neg_distrib]
    _ = 0 := by
      rw [hPressure]
      simp

end

end Euclidean
end Bridge
end PrimeTensor
