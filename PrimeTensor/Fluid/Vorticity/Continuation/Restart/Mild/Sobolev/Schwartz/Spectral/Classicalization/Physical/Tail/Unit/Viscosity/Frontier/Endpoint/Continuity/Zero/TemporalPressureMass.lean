import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureDefect

/-!
# Zeroth-order endpoint continuity: temporal mass splits into projected RHS plus pressure defect

`TemporalPressureDefect` gives the exact pointwise identity

    ∂ₜu_i
      =
    R_i - G_i,

where

* `R_i = Δu_i - (P div(u ⊗ u))_i` is the already-constructed
  endpoint-independent projected RHS; and
* `G_i = ∂ᵢp_old - ∂ᵢp_can` is the old-vs-canonical pressure-gradient defect.

This file turns that pointwise identity into the corresponding compact-test
spatial norm-mass inequality

    M_temporal ≤ M_projectedRHS + M_pressureDefect.

All three compactly tested spatial slices are integrable at each closed elapsed
time.  The projected term is integrable because its Laplacian and Leray-forcing
pieces already are; the pressure defect is continuous in space at each
preterminal slice and therefore becomes integrable after multiplication by a
compact smooth test.

No endpoint continuity or time integration is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldTemporalPressureMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldTemporalPressureMass :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Literal endpoint-independent projected RHS coordinate at one old elapsed
slice. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    ℝ :=
  (PrimeTensor.Bridge.RealFluid.laplacianVector
    spatial3
    (logSpaceTimeVectorField u)
    (t + (q : ℝ))
    x).component
      (h3AxisOfFin3 i)
    -
  (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
    (h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q)
    (h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q)
    i x).re

/-- Compact-test spatial `L¹` norm mass of the literal projected RHS. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
        hNS ht hEnd hTail q i x)‖
    ∂volume

/-- Compact-test spatial `L¹` norm mass of the old-vs-canonical pressure
gradient defect. -/
noncomputable def h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    ℝ :=
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
        hNS ht hEnd hTail q i x)‖
    ∂volume

/-- The compactly tested literal projected RHS is spatially integrable on every
closed elapsed slice. -/
theorem h3WeakTest_mul_zeroProjectedLiteralRHS_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
            hNS ht hEnd hTail q i x))
      (volume : Measure Point3) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  have hLap :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            ((PrimeTensor.Bridge.RealFluid.laplacianVector
              spatial3
              (logSpaceTimeVectorField u)
              (t + (q : ℝ))
              x).component
                (h3AxisOfFin3 i)))
        (volume : Measure Point3) :=
    h3PreterminalLoggedVelocity_test_mul_laplacianVector_integrable
      hNS ht hEnd hTail q i ψ

  have hForce :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re))
        (volume : Measure Point3) :=
    h3RawFinLerayOuterProductDivergenceWeakPairing_integrable
      ψ i U

  have hSub := hLap.sub hForce

  dsimp only [U] at hSub

  have hSubPoint :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              ((PrimeTensor.Bridge.RealFluid.laplacianVector
                spatial3
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                x).component
                  (h3AxisOfFin3 i))
            -
          (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q)
                (h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q)
                i x).re))
        (volume : Measure Point3) := by
    change
      Integrable
        ((fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              ((PrimeTensor.Bridge.RealFluid.laplacianVector
                spatial3
                (logSpaceTimeVectorField u)
                (t + (q : ℝ))
                x).component
                  (h3AxisOfFin3 i)))
          -
         (fun x : Point3 =>
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              ((h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
                (h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q)
                (h3PreterminalTailCanonicalSpectralStateOnElapsed
                  hNS ht hEnd hTail q)
                i x).re)))
        (volume : Measure Point3)

    exact hSub

  unfold h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed

  simpa only [map_sub] using hSubPoint

/-- The compactly tested pressure-gradient defect is spatially integrable on
every closed elapsed slice. -/
theorem h3WeakTest_mul_zeroPressureGradientDefect_integrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    Integrable
      (fun x : Point3 =>
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
            hNS ht hEnd hTail q i x))
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
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hOldC2 :
      SpatialC2
        (pOld (t + (q : ℝ))) :=
    hPDE.regularity.pressure_spatial_two
      (t + (q : ℝ)) hAbs

  have hOldC1 :
      SpatialC1
        (pOld (t + (q : ℝ))) :=
    hOldC2.of_le (by norm_num)

  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  let pCan :
      ScalarField3 :=
    h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
      hNS ht hEnd hTail q

  have hCanC1 :
      SpatialC1 pCan := by
    dsimp only [
      pCan,
      h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed,
      W,
      U
    ]

    exact
      h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)
        (h3PreterminalTailCanonicalSpectralStateOnElapsed
          hNS ht hEnd hTail q)

  have hOldD :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          (pOld (t + (q : ℝ)))) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hOldC1
      (h3AxisOfFin3 i)

  have hCanD :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          pCan) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hCanC1
      (h3AxisOfFin3 i)

  have hDef :
      Continuous
        (fun x : Point3 =>
          spatial3.d
              (h3AxisOfFin3 i)
              (pOld (t + (q : ℝ)))
              x
            -
          spatial3.d
              (h3AxisOfFin3 i)
              pCan
              x) :=
    hOldD.sub hCanD

  have hInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (spatial3.d
                (h3AxisOfFin3 i)
                (pOld (t + (q : ℝ)))
                x
              -
             spatial3.d
                (h3AxisOfFin3 i)
                pCan
                x))
        (volume : Measure Point3) :=
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hDef.locallyIntegrable.locallyIntegrableOn Set.univ)

  dsimp only [pCan] at hInt
  unfold h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed

  simpa only [pOld] using hInt

/-- Pointwise compact-test norm inequality corresponding to
`∂ₜu = projectedRHS - pressureDefect`. -/
theorem norm_h3WeakTest_mul_loggedTemporalDerivative_le_projectedRHS_add_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction)
    (x : Point3) :
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent
              u a (h3AxisOfFin3 i) x)
          (t + (q : ℝ)))‖
      ≤
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
          hNS ht hEnd hTail q i x)‖
      +
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
          hNS ht hEnd hTail q i x)‖ := by
  have hTemporal :=
    h3PreterminalLoggedVelocity_temporalDerivative_eq_zeroProjectedLiteralRHS_sub_pressureGradientDefect
      hNS ht hEnd hTail q i x

  have hMapped :
      (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))
        =
      (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
            hNS ht hEnd hTail q i x)
        -
      (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
            hNS ht hEnd hTail q i x) := by
    unfold h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
    rw [hTemporal, map_sub]

  rw [hMapped]

  exact norm_sub_le _ _

/-- The compact-test spatial norm mass of the actual old temporal derivative is
bounded by the sum of the projected-RHS mass and the pressure-defect mass. -/
theorem h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed_le_projectedRHS_add_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
        hNS t i ψ (q : ℝ)
      ≤
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      +
    h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ := by
  have hTemp :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (temporal.d
              (fun a : ℝ =>
                loggedVelocityComponent
                  u a (h3AxisOfFin3 i) x)
              (t + (q : ℝ))))
        (volume : Measure Point3) :=
    h3PreterminalLoggedVelocity_test_mul_temporalDerivative_integrable
      hNS ht hEnd hTail q i ψ

  have hRHS :=
    h3WeakTest_mul_zeroProjectedLiteralRHS_integrable
      hNS ht hEnd hTail q i ψ

  have hDef :=
    h3WeakTest_mul_zeroPressureGradientDefect_integrable
      hNS ht hEnd hTail q i ψ

  have hAbs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T :=
    h3PreterminalElapsedTime_mem_Ioo
      ht hEnd q

  have hMassActual :
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed
          hNS t i ψ (q : ℝ)
        =
      ∫ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))‖
        ∂volume := by
    unfold
      h3PreterminalLoggedVelocityTemporalSpatialNormMassOnElapsed

    apply integral_congr_ae
    filter_upwards with x

    rw [
      h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_apply_of_mem
        hNS i hAbs x
    ]

  rw [hMassActual]

  unfold
    h3PreterminalTailCanonicalZeroProjectedRHSSpatialNormMassOnElapsed
    h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed

  have hMajor :
      Integrable
        (fun x : Point3 =>
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
                hNS ht hEnd hTail q i x)‖
            +
          ‖(ContinuousLinearMap.lsmul ℝ ℝ)
              (ψ x)
              (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
                hNS ht hEnd hTail q i x)‖)
        (volume : Measure Point3) :=
    hRHS.norm.add hDef.norm

  have hIntegralLe :
      (∫ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (temporal.d
            (fun a : ℝ =>
              loggedVelocityComponent
                u a (h3AxisOfFin3 i) x)
            (t + (q : ℝ)))‖
        ∂volume)
        ≤
      ∫ x : Point3,
        (‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
              hNS ht hEnd hTail q i x)‖
          +
         ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
              hNS ht hEnd hTail q i x)‖)
        ∂volume := by
    exact
      integral_mono_ae
        hTemp.norm
        hMajor
        (Filter.Eventually.of_forall
          (fun x =>
            norm_h3WeakTest_mul_loggedTemporalDerivative_le_projectedRHS_add_pressureDefect
              hNS ht hEnd hTail q i ψ x))

  calc
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (temporal.d
          (fun a : ℝ =>
            loggedVelocityComponent
              u a (h3AxisOfFin3 i) x)
          (t + (q : ℝ)))‖
      ∂volume)
      ≤
    ∫ x : Point3,
      (‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
            hNS ht hEnd hTail q i x)‖
        +
       ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
            hNS ht hEnd hTail q i x)‖)
      ∂volume :=
      hIntegralLe
    _ =
      (∫ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroProjectedLiteralRHSOnElapsed
            hNS ht hEnd hTail q i x)‖
        ∂volume)
        +
      ∫ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
            hNS ht hEnd hTail q i x)‖
        ∂volume := by
      exact integral_add hRHS.norm hDef.norm

end

end Euclidean
end Bridge
end PrimeTensor
