import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureSplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.L1.Bound
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.Fresh.Rescaled.Continuity

/-!
# Zeroth-order endpoint continuity: close canonical pressure-gradient mass

`TemporalPressureSplit` separated the remaining pressure-gradient defect mass
into

    M_defect <= M_old + M_can.

This file closes the canonical term quantitatively from the retained H³ tail.

For one old canonical H³ snapshot `U`, the exact spectral pressure-force
identity gives

    -∂ᵢ p_can
      =
    Re F⁻¹ div(U ⊗ U)ᵢ
      -
    Re F⁻¹ P div(U ⊗ U)ᵢ.

The unprojected inverse-Fourier term is bounded pointwise by its Fourier `L¹`
mass, while the projected continuous representative already has the bilinear
pointwise bound.  The retained tail ceiling supplies

    ‖U‖ <= 2E.

Thus every canonical pressure-gradient coordinate has a uniform pointwise
bound depending only on `E`.  Multiplication by a fixed compact smooth weak
test and integration gives a uniform spatial mass bound.

Consequently the all-divergence-free canonical pressure-gradient mass frontier
is closed outright.  The zeroth-order pressure-defect frontier is therefore
reduced to the old preterminal pressure-gradient mass alone.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureCanonicalBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroTemporalPressureCanonicalBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Generic fixed-point inverse-Fourier estimate by Fourier `L¹` mass. -/
theorem norm_h3FourierInv_le_integral_norm_zeroCanonicalPressure
    (F : H3FourierPoint3 → ℂ)
    (hF : Integrable F (volume : Measure H3FourierPoint3))
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv F x‖
      ≤
    ∫ ξ : H3FourierPoint3, ‖F ξ‖ := by
  have hInnerContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          inner ℝ ξ x) := by
    fun_prop

  have hPhaseContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp hInnerContinuous

  have hPhaseMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • F ξ)
        (volume : Measure H3FourierPoint3) :=
    hPhaseContinuous.aestronglyMeasurable.fun_smul hF.1

  have hPhaseInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          Real.fourierChar (inner ℝ ξ x) • F ξ)
        (volume : Measure H3FourierPoint3) := by
    rw [← integrable_norm_iff hPhaseMeas]
    simpa only [Circle.norm_smul] using hF.norm

  rw [Real.fourierInv_eq]

  calc
    ‖∫ ξ : H3FourierPoint3,
        Real.fourierChar (inner ℝ ξ x) • F ξ‖
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖Real.fourierChar (inner ℝ ξ x) • F ξ‖ :=
      norm_integral_le_integral_norm _
    _ =
      ∫ ξ : H3FourierPoint3, ‖F ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Circle.norm_smul]

/-- Pointwise bound for the unprojected raw nonlinear divergence reconstruction. -/
theorem norm_h3RawFinOuterProductDivergence_fourierInv_le
    (U : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    ‖FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence U U i)
        x‖
      ≤
    3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖U‖ := by
  exact
    (norm_h3FourierInv_le_integral_norm_zeroCanonicalPressure
      (h3RawFinOuterProductDivergence U U i)
      (h3RawFinOuterProductDivergence_integrable U U i)
      x).trans
      (h3RawFinOuterProductDivergence_norm_integral_le U U i)

/-- Uniform pointwise ceiling for one canonical pressure-gradient coordinate. -/
noncomputable def h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound
    (E : ℝ) : ℝ :=
  (3 * h3RawProductDerivativeL1Coefficient
      + h3NonlinearForcingL1Coefficient)
    *
  (2 * E) ^ 2

theorem h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound_nonneg
    (E : ℝ) :
    0 ≤ h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E := by
  unfold h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound

  exact
    mul_nonneg
      (add_nonneg
        (mul_nonneg
          (by norm_num)
          h3RawProductDerivativeL1Coefficient_nonneg)
        h3NonlinearForcingL1Coefficient_nonneg)
      (sq_nonneg (2 * E))

/-- The canonical snapshot pressure gradient is uniformly pointwise bounded
from the retained H³ energy ceiling. -/
theorem norm_h3PreterminalTailCanonicalZeroSnapshotPressure_spatial_d_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (x : Point3) :
    ‖spatial3.d
        (h3AxisOfFin3 i)
        (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
          hNS ht hEnd hTail q)
        x‖
      ≤
    h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E := by
  let U : H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSpectralStateOnElapsed
      hNS ht hEnd hTail q

  let W : ℝ → H3SpectralFinVectorState :=
    fun _ => U

  let ξx : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  have hPressure :=
    h3RawFinPressureRealC1OfPath_pressureForceComponent_eq_raw_sub_leray
      W 0 i x

  have hPressure' :
      -
      spatial3.d
        (h3AxisOfFin3 i)
        (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
          hNS ht hEnd hTail q)
        x
        =
      (FourierTransformInv.fourierInv
        (h3RawFinOuterProductDivergence U U i)
        ξx).re
        -
      (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
        U U i x).re := by
    simpa only [
      PrimeTensor.Bridge.RealFluid.pressureForceComponent,
      h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed,
      h3RawFinPressureRealC1OfPath,
      W,
      U,
      ξx
    ] using hPressure

  have hRaw :
      ‖FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence U U i)
          ξx‖
        ≤
      3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖U‖ :=
    norm_h3RawFinOuterProductDivergence_fourierInv_le U i ξx

  have hLeray :
      ‖h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x‖
        ≤
      h3NonlinearForcingL1Coefficient * ‖U‖ * ‖U‖ := by
    unfold h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
    exact
      norm_h3RawFinLerayOuterProductDivergenceC0Representative_le_bilinear
        (ν := (1 : ℝ)) (by norm_num) U U i ξx

  have hRawRe :
      abs
        (FourierTransformInv.fourierInv
          (h3RawFinOuterProductDivergence U U i)
          ξx).re
        ≤
      3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖U‖ :=
    (Complex.abs_re_le_norm _).trans hRaw

  have hLerayRe :
      abs
        (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
          U U i x).re
        ≤
      h3NonlinearForcingL1Coefficient * ‖U‖ * ‖U‖ :=
    (Complex.abs_re_le_norm _).trans hLeray

  have hGradU :
      ‖spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x‖
        ≤
      (3 * h3RawProductDerivativeL1Coefficient
          + h3NonlinearForcingL1Coefficient)
        *
      (‖U‖ * ‖U‖) := by
    calc
      ‖spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x‖
          =
        ‖-
          spatial3.d
            (h3AxisOfFin3 i)
            (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
              hNS ht hEnd hTail q)
            x‖ := by
              rw [norm_neg]
      _ =
        abs
          ((FourierTransformInv.fourierInv
              (h3RawFinOuterProductDivergence U U i)
              ξx).re
            -
           (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
              U U i x).re) := by
              rw [hPressure']
              rfl
      _ ≤
        abs
          (FourierTransformInv.fourierInv
            (h3RawFinOuterProductDivergence U U i)
            ξx).re
          +
        abs
          (h3RawFinLerayOuterProductDivergenceC0RepresentativeOnPoint3
            U U i x).re :=
        abs_sub _ _
      _ ≤
        (3 * h3RawProductDerivativeL1Coefficient * ‖U‖ * ‖U‖)
          +
        (h3NonlinearForcingL1Coefficient * ‖U‖ * ‖U‖) :=
        add_le_add hRawRe hLerayRe
      _ =
        (3 * h3RawProductDerivativeL1Coefficient
            + h3NonlinearForcingL1Coefficient)
          *
        (‖U‖ * ‖U‖) := by
            ring

  have hU :
      ‖U‖ ≤ 2 * E := by
    dsimp only [U]
    exact
      norm_h3PreterminalTailCanonicalSpectralStateOnElapsed_le_twoE
        hNS ht hEnd hE hTail q

  have hTwoE :
      0 ≤ 2 * E := by
    nlinarith [hE]

  have hUSq :
      ‖U‖ * ‖U‖
        ≤
      (2 * E) ^ 2 := by
    have hUnonneg : 0 ≤ ‖U‖ := norm_nonneg U
    nlinarith

  have hCoeff :
      0 ≤
        3 * h3RawProductDerivativeL1Coefficient
          + h3NonlinearForcingL1Coefficient :=
    add_nonneg
      (mul_nonneg
        (by norm_num)
        h3RawProductDerivativeL1Coefficient_nonneg)
      h3NonlinearForcingL1Coefficient_nonneg

  exact
    hGradU.trans
      (by
        unfold h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound
        exact
          mul_le_mul_of_nonneg_left
            hUSq
            hCoeff)

/-- Uniform compact-test mass bound for one canonical pressure-gradient
coordinate. -/
theorem h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3)
    (ψ : H3WeakTestFunction) :
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i ψ
      ≤
    h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E
      *
    h3WeakTestFunctionL1Mass ψ := by
  let B : ℝ :=
    h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E

  have hB :
      0 ≤ B := by
    dsimp only [B]
    exact
      h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound_nonneg E

  have hTargetInt :=
    (h3WeakTest_mul_zeroCanonicalPressureGradient_integrable
      hNS ht hEnd hTail q i ψ).norm

  have hPsiInt :
      Integrable
        (fun x : Point3 => ‖ψ x‖)
        (volume : Measure Point3) :=
    (h3WeakTestFunction_integrable ψ).norm

  have hMajorInt :
      Integrable
        (fun x : Point3 => B * ‖ψ x‖)
        (volume : Measure Point3) :=
    hPsiInt.const_mul B

  have hPoint :
      ∀ x : Point3,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ)
            (ψ x)
            (spatial3.d
              (h3AxisOfFin3 i)
              (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
                hNS ht hEnd hTail q)
              x)‖
          ≤
        B * ‖ψ x‖ := by
    intro x

    have hGrad :=
      norm_h3PreterminalTailCanonicalZeroSnapshotPressure_spatial_d_le
        hNS ht hEnd hE hTail q i x

    change
      ‖ψ x *
        spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x‖
        ≤
      B * ‖ψ x‖

    rw [norm_mul]

    calc
      ‖ψ x‖ *
          ‖spatial3.d
            (h3AxisOfFin3 i)
            (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
              hNS ht hEnd hTail q)
            x‖
          ≤
        ‖ψ x‖ * B :=
        mul_le_mul_of_nonneg_left
          hGrad
          (norm_nonneg (ψ x))
      _ = B * ‖ψ x‖ := by
        ring

  unfold
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed

  calc
    (∫ x : Point3,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ)
        (ψ x)
        (spatial3.d
          (h3AxisOfFin3 i)
          (h3PreterminalTailCanonicalZeroSnapshotPressureOnElapsed
            hNS ht hEnd hTail q)
          x)‖
      ∂volume)
        ≤
      ∫ x : Point3, B * ‖ψ x‖ ∂volume := by
        exact
          integral_mono_ae
            hTargetInt
            hMajorInt
            (Filter.Eventually.of_forall hPoint)
    _ =
      B * h3WeakTestFunctionL1Mass ψ := by
        unfold h3WeakTestFunctionL1Mass
        rw [integral_const_mul]
    _ =
      h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E
        *
      h3WeakTestFunctionL1Mass ψ := by
        rfl

/-- Finite-coordinate aggregate canonical pressure-gradient mass ceiling for one
weak-test vector. -/
noncomputable def h3UnitViscosityZeroCanonicalPressureWeakTestMassBound
    (E : ℝ)
    (φ : H3WeakTestVector) : ℝ :=
  ∑ i : Fin 3,
    h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E
      *
    h3WeakTestFunctionL1Mass (φ i)

theorem h3WeakTestFunctionL1Mass_nonneg_zeroCanonicalPressure
    (ψ : H3WeakTestFunction) :
    0 ≤ h3WeakTestFunctionL1Mass ψ := by
  unfold h3WeakTestFunctionL1Mass
  exact integral_nonneg (fun x => norm_nonneg (ψ x))

theorem h3UnitViscosityZeroCanonicalPressureWeakTestMassBound_nonneg
    (E : ℝ)
    (φ : H3WeakTestVector) :
    0 ≤
      h3UnitViscosityZeroCanonicalPressureWeakTestMassBound E φ := by
  unfold h3UnitViscosityZeroCanonicalPressureWeakTestMassBound

  exact
    Finset.sum_nonneg
      (fun i hi =>
        mul_nonneg
          (h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound_nonneg E)
          (h3WeakTestFunctionL1Mass_nonneg_zeroCanonicalPressure (φ i)))

/-- Every coordinate canonical pressure-gradient mass is bounded by the
finite-coordinate aggregate ceiling. -/
theorem h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed_le_aggregate
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed
        hNS ht hEnd hTail q i (φ i)
      ≤
    h3UnitViscosityZeroCanonicalPressureWeakTestMassBound E φ := by
  have hCoord :=
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed_le
      hNS ht hEnd hE hTail q i (φ i)

  have hSingle :
      h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E
          *
        h3WeakTestFunctionL1Mass (φ i)
        ≤
      ∑ j : Fin 3,
        h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound E
          *
        h3WeakTestFunctionL1Mass (φ j) := by
    exact
      Finset.single_le_sum
        (fun j _ =>
          mul_nonneg
            (h3UnitViscosityZeroCanonicalPressureGradientPointwiseBound_nonneg E)
            (h3WeakTestFunctionL1Mass_nonneg_zeroCanonicalPressure (φ j)))
        (Finset.mem_univ i)

  exact
    hCoord.trans
      (by
        simpa only [
          h3UnitViscosityZeroCanonicalPressureWeakTestMassBound
        ] using hSingle)

/-- The canonical pressure-gradient mass frontier is closed for every weak-test
vector; divergence-freeness is not needed for this estimate. -/
theorem H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed_proved
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector) :
    H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail φ := by
  refine
    ⟨
      h3UnitViscosityZeroCanonicalPressureWeakTestMassBound E φ,
      ?_
    ⟩

  intro i q

  exact
    h3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassOnElapsed_le_aggregate
      hNS ht hEnd hE hTail φ q i

/-- Hence the all-divergence-free canonical pressure-gradient mass frontier is
fully closed. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsCanonicalPressureGradientMassUniformlyBoundedOnElapsed_proved
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsCanonicalPressureGradientMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  intro φ hφ

  exact
    H3PreterminalTailCanonicalZeroCanonicalPressureGradientSpatialNormMassUniformlyBoundedOnElapsed_proved
      hNS ht hEnd hE hTail φ

/-- Once the canonical side is discharged, the current pressure-defect frontier
requires only uniform old-pressure-gradient mass. -/
theorem H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_oldPressure
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
      hNS ht hEnd hTail := by
  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_old_of_canonical
      hNS ht hEnd hTail
      hOld
      (H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsCanonicalPressureGradientMassUniformlyBoundedOnElapsed_proved
        hNS ht hEnd hE hTail)

end

end Euclidean
end Bridge
end PrimeTensor
