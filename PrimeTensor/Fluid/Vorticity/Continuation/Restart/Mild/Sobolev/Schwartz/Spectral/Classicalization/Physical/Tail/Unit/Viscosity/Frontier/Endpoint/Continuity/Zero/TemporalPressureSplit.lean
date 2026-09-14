import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureFamilyFrontier

/-!
# Zeroth-order endpoint continuity: split the pressure-gradient defect mass

The current zeroth-order continuation frontier is the uniform compact-test mass
of

    ∂ᵢ p_old - ∂ᵢ p_can.

This file separates that quantity into its two natural pieces.

For a fixed scalar weak test `ψ`, define

    M_old(q,i,ψ) = ∫ ‖ψ ∂ᵢ p_old(q)‖,
    M_can(q,i,ψ) = ∫ ‖ψ ∂ᵢ p_can(q)‖.

Both are finite at every elapsed slice because the old pressure is spatial `C²`
and the canonical pressure is spatial `C¹`, while `ψ` is compactly supported.

The triangle inequality gives

    M_defect ≤ M_old + M_can.

Consequently, uniform bounds for the old and canonical pressure-gradient masses
separately imply the existing pressure-defect mass frontier.  This isolates the
two sources cleanly:

* the canonical side depends only on the H³ snapshot construction;
* the old side is the only place where the preterminal pressure choice remains.

No time regularity of either pressure is assumed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroTemporalPressureSplit :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Compact-test spatial `L¹` norm mass of the old pressure gradient. -/
noncomputable def h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
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
  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  ∫ x : Point3,
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ x)
      (spatial3.d
        (h3AxisOfFin3 i)
        (pOld (t + (q : ℝ)))
        x)‖
    ∂volume

/-- Compact-test spatial `L¹` norm mass of the canonical snapshot pressure
gradient. -/
noncomputable def h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
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
      (spatial3.d
        (h3AxisOfFin3 i)
        (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
          hNS ht hEnd hTail q)
        x)‖
    ∂volume

/-- The old pressure gradient multiplied by a compact smooth test is spatially
integrable at every elapsed slice. -/
theorem h3WeakTest_mul_zeroOldPressureGradient_integrable
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
        let pOld :
            SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
          Classical.choose hNS
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (ψ x)
          (spatial3.d
            (h3AxisOfFin3 i)
            (pOld (t + (q : ℝ)))
            x))
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

  have hOldD :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          (pOld (t + (q : ℝ)))) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hOldC1
      (h3AxisOfFin3 i)

  have hInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (pOld (t + (q : ℝ)))
              x))
        (volume : Measure Point3) :=
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hOldD.locallyIntegrable.locallyIntegrableOn Set.univ)

  simpa only [pOld] using hInt

/-- The canonical snapshot pressure gradient multiplied by a compact smooth
test is spatially integrable at every elapsed slice. -/
theorem h3WeakTest_mul_zeroCanonicalPressureGradient_integrable
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
          (spatial3.d
            (h3AxisOfFin3 i)
            (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
              hNS ht hEnd hTail q)
            x))
      (volume : Measure Point3) := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  let pCan : ScalarField3 :=
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

  have hCanD :
      Continuous
        (spatial3.d
          (h3AxisOfFin3 i)
          pCan) :=
    h3SpatialC1_spatial3_d_continuous_weakPressure
      hCanC1
      (h3AxisOfFin3 i)

  have hInt :
      Integrable
        (fun x : Point3 =>
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (spatial3.d
              (h3AxisOfFin3 i)
              pCan
              x))
        (volume : Measure Point3) :=
    ψ.integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (hCanD.locallyIntegrable.locallyIntegrableOn Set.univ)

  dsimp only [pCan] at hInt
  exact hInt

/-- The pressure-gradient defect mass is bounded by the sum of its old and
canonical pressure-gradient masses. -/
theorem h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed_le_old_add_canonical
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
    h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      ≤
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      +
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ := by
  have hDefInt :=
    (h3WeakTest_mul_zeroPressureGradientDefect_integrable
      hNS ht hEnd hTail q i ψ).norm

  have hOldInt :=
    (h3WeakTest_mul_zeroOldPressureGradient_integrable
      hNS ht hEnd hTail q i ψ).norm

  have hCanInt :=
    (h3WeakTest_mul_zeroCanonicalPressureGradient_integrable
      hNS ht hEnd hTail q i ψ).norm

  unfold
    h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed
    h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed

  let pOld :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  change
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
            (h3AxisOfFin3 i)
            (pOld (t + (q : ℝ)))
            x
          -
         spatial3.d
            (h3AxisOfFin3 i)
            (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
              hNS ht hEnd hTail q)
            x)‖
      ∂volume)
      ≤
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          (h3AxisOfFin3 i)
          (pOld (t + (q : ℝ)))
          x)‖
      ∂volume)
      +
    ∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x)‖
      ∂volume

  rw [← integral_add hOldInt hCanInt]

  apply integral_mono_ae hDefInt (hOldInt.add hCanInt)

  filter_upwards with x

  have hDefPoint :
      h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
          hNS ht hEnd hTail q i x
        =
      spatial3.d
          (h3AxisOfFin3 i)
          (pOld (t + (q : ℝ)))
          x
        -
      spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x := by
    rfl

  change
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (h3PreterminalTailCanonicalZeroPressureGradientDefectOnElapsed
          hNS ht hEnd hTail q i x)‖
      ≤
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          (h3AxisOfFin3 i)
          (pOld (t + (q : ℝ)))
          x)‖
      +
    ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x)‖

  rw [hDefPoint, map_sub]

  exact norm_sub_le _ _

/-- Uniform compact-test old pressure-gradient mass on one closed elapsed
interval. -/
def H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) : Prop :=
  ∃ C : ℝ,
    ∀ (i : Fin 3) (q : Set.Icc (0 : ℝ) tau),
      h3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassOnElapsed
          hNS ht hEnd hTail q i (φ i)
        ≤
      C

/-- Uniform compact-test canonical pressure-gradient mass on one closed elapsed
interval. -/
def H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) : Prop :=
  ∃ C : ℝ,
    ∀ (i : Fin 3) (q : Set.Icc (0 : ℝ) tau),
      h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
          hNS ht hEnd hTail q i (φ i)
        ≤
      C

/-- Separate uniform old and canonical pressure-gradient mass bounds imply the
existing pressure-defect mass frontier for one weak-test vector. -/
theorem H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed_of_old_of_canonical
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hOld :
      H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ)
    (hCan :
      H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ := by
  rcases hOld with ⟨COld, hCOld⟩
  rcases hCan with ⟨CCan, hCCan⟩

  refine ⟨COld + CCan, ?_⟩
  intro i q

  exact
    (h3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassOnElapsed_le_old_add_canonical
      hNS ht hEnd hTail q i (φ i)).trans
      (add_le_add
        (hCOld i q)
        (hCCan i q))

/-- All-divergence-free old pressure-gradient mass frontier on one elapsed
interval. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PreterminalTailCanonicalZeroOldPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ

/-- All-divergence-free canonical pressure-gradient mass frontier on one
elapsed interval. -/
def H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsCanonicalPressureGradientMassUniformlyBoundedOnElapsed
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ φ : H3WeakTestVector,
    H3WeakTestVectorDivergenceFree φ →
    H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ

/-- The two separated all-test pressure-gradient mass frontiers imply the
current all-test pressure-defect mass frontier. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_old_of_canonical
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (hCan :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsCanonicalPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ

  exact
    H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed_of_old_of_canonical
      hNS ht hEnd hTail φ
      (hOld φ hφ)
      (hCan φ hφ)

end

end Euclidean
end Bridge
end PrimeTensor
