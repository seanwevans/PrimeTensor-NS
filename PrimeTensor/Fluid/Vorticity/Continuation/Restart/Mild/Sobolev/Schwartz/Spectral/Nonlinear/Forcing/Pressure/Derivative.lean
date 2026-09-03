import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.C1
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.Point3Derivative
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Coordinate derivatives of the H³ pressure representative

`Pressure.C1` constructs the canonical pressure

    p = 𝓕⁻ p̂

from the Leray-complement multiplier and proves that `p` is spatially `C¹`.

This file identifies its coordinate derivatives exactly.  The proof follows the
same Fourier line-derivative route already used for arbitrary H³ scalar states:
the first pressure Fourier moment gives Mathlib's Fréchet derivative formula,
composition with inverse Fourier contributes the expected sign, and evaluation
on the intrinsic coordinate direction yields multiplication by PrimeTensor's
Fourier derivative symbol.

Thus

    ∂ᵢ p
      =
    𝓕⁻(dᵢ p̂).

The algebraic pressure multiplier theorem already proved

    P F = F + d p̂,

so

    dᵢ p̂ = (P F)ᵢ - Fᵢ.

After transport to `Point3`, the pressure derivative is therefore exactly the
real inverse Fourier reconstruction of the Leray forcing minus the raw forcing.
This is the precise pressure-gradient bridge needed by the physical momentum
equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal FourierTransform LineDeriv

noncomputable section

noncomputable local instance axisFintypeH3PressureDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- One coordinate Fourier derivative of the pressure amplitude. -/
noncomputable def h3RawFinPressureFourierCoordinateDerivative
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  fun ξ =>
    h3FourierDerivativeSymbol i ξ *
      h3RawFinPressureFourier U V ξ

/-- The pressure coordinate derivative multiplier is integrable. -/
theorem h3RawFinPressureFourierCoordinateDerivative_integrable
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (h3RawFinPressureFourierCoordinateDerivative U V i)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3RawFinPressureFourier U V ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinPressureFourier_firstMoment_integrable U V

  have hDom :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ * ‖h3RawFinPressureFourier U V ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (2 * Real.pi)

  apply hDom.mono'
  · exact
      (h3FourierDerivativeSymbol_continuous i).aestronglyMeasurable.mul
        (h3RawFinPressureFourier_integrable U V).aestronglyMeasurable
  · filter_upwards with ξ
    unfold h3RawFinPressureFourierCoordinateDerivative
    calc
      ‖h3FourierDerivativeSymbol i ξ *
          h3RawFinPressureFourier U V ξ‖
          =
        ‖h3FourierDerivativeSymbol i ξ‖ *
          ‖h3RawFinPressureFourier U V ξ‖ := by
            rw [norm_mul]
      _ ≤
        h3FourierGradientMagnitude ξ *
          ‖h3RawFinPressureFourier U V ξ‖ :=
        mul_le_mul_of_nonneg_right
          (norm_h3FourierDerivativeSymbol_le_gradientMagnitude i ξ)
          (norm_nonneg _)
      _ =
        (2 * Real.pi) *
          (‖ξ‖ * ‖h3RawFinPressureFourier U V ξ‖) := by
            unfold h3FourierGradientMagnitude
            ring

/-- The vector-valued Fourier derivative integrand for the pressure amplitude is
integrable. -/
theorem h3RawFinPressureFourier_fourierSMulRight_integrable
    (U V : H3SpectralFinVectorState) :
    Integrable
      (VectorFourier.fourierSMulRight
        (innerSL ℝ)
        (h3RawFinPressureFourier U V))
      (volume : Measure H3FourierPoint3) := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinPressureFourier U V

  have hf :
      Integrable f (volume : Measure H3FourierPoint3) := by
    simpa only [f] using h3RawFinPressureFourier_integrable U V

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3RawFinPressureFourier_firstMoment_integrable U V

  have hDom :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖) *
            (‖ξ‖ * ‖f ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul
      (2 * Real.pi * ‖innerSL (E := H3FourierPoint3) ℝ‖)

  apply hDom.mono'
  · exact hf.aestronglyMeasurable.fourierSMulRight
  · filter_upwards with ξ
    calc
      ‖VectorFourier.fourierSMulRight
          (innerSL ℝ) f ξ‖
          ≤
        2 * Real.pi *
          ‖innerSL (E := H3FourierPoint3) ℝ‖ *
          ‖ξ‖ * ‖f ξ‖ :=
        VectorFourier.norm_fourierSMulRight_le
          (innerSL ℝ) f ξ
      _ =
        (2 * Real.pi *
          ‖innerSL (E := H3FourierPoint3) ℝ‖) *
          (‖ξ‖ * ‖f ξ‖) := by
            ring

/-- Coordinate line derivative of the complex pressure inverse-Fourier
representative. -/
theorem h3RawFinPressureC1Representative_hasLineDerivAt_fin
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasLineDerivAt ℝ
      (h3RawFinPressureC1Representative U V)
      (FourierTransformInv.fourierInv
        (h3RawFinPressureFourierCoordinateDerivative U V i)
        x)
      x
      (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
  let f : H3FourierPoint3 → ℂ :=
    h3RawFinPressureFourier U V

  let v : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 i)

  have hf :
      Integrable f (volume : Measure H3FourierPoint3) := by
    simpa only [f] using h3RawFinPressureFourier_integrable U V

  have hMoment :
      Integrable
        (fun ξ : H3FourierPoint3 => ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3RawFinPressureFourier_firstMoment_integrable U V

  have hFourier :
      HasFDerivAt
        (FourierTransform.fourier f)
        (FourierTransform.fourier
          (VectorFourier.fourierSMulRight
            (innerSL ℝ) f)
          (-x))
        (-x) :=
    Real.hasFDerivAt_fourier hf hMoment (-x)

  have hComp :=
    hFourier.comp
      x
      ((hasFDerivAt_id x).neg)

  have hLine :=
    hComp.hasLineDerivAt v

  have hSMulInt :
      Integrable
        (VectorFourier.fourierSMulRight
          (innerSL ℝ) f)
        (volume : Measure H3FourierPoint3) := by
    simpa only [f] using
      h3RawFinPressureFourier_fourierSMulRight_integrable U V

  have hDerivativeValue :
      ((FourierTransform.fourier
          (VectorFourier.fourierSMulRight
            (innerSL ℝ) f)
          (-x)).comp
        (-ContinuousLinearMap.id ℝ H3FourierPoint3))
        v
        =
      FourierTransformInv.fourierInv
        (h3RawFinPressureFourierCoordinateDerivative U V i)
        x := by
    rw [ContinuousLinearMap.comp_apply]
    simp only [
      neg_apply,
      ContinuousLinearMap.id_apply
    ]

    rw [Real.fourier_continuousLinearMap_apply hSMulInt]
    rw [Real.fourierInv_eq_fourier_neg]

    apply Real.fourier_congr_ae
    filter_upwards with ξ

    unfold h3RawFinPressureFourierCoordinateDerivative
    rw [h3FourierDerivativeSymbol_eq_inner]

    simp only [
      VectorFourier.fourierSMulRight_apply,
      v,
      smul_eq_mul
    ]

    rw [map_neg, innerSL_apply_apply]
    dsimp [f]
    push_cast
    ring

  rw [hDerivativeValue] at hLine

  have hRepresentativeEq :
      h3RawFinPressureC1Representative U V
        =
      (FourierTransform.fourier f ∘ Neg.neg) := by
    funext y
    unfold h3RawFinPressureC1Representative
    change
      FourierTransformInv.fourierInv
          (h3RawFinPressureFourier U V) y
        =
      FourierTransform.fourier f (-y)
    simpa only [f] using
      Real.fourierInv_eq_fourier_neg
        (h3RawFinPressureFourier U V) y

  rw [hRepresentativeEq]
  simpa only [f, v] using hLine

/-- Taking real parts carries the exact pressure coordinate derivative to the
real pressure representative on the Fourier carrier. -/
theorem h3RawFinPressureRealC1Representative_hasLineDerivAt_fin
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasLineDerivAt ℝ
      (h3RawFinPressureRealC1Representative U V)
      ((FourierTransformInv.fourierInv
        (h3RawFinPressureFourierCoordinateDerivative U V i)
        x).re)
      x
      (h3FourierAxisDirection (h3AxisOfFin3 i)) := by
  have hComplex :=
    h3RawFinPressureC1Representative_hasLineDerivAt_fin
      U V i x

  unfold HasLineDerivAt at hComplex ⊢

  have hReal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ)
      hComplex

  simpa only [
    h3RawFinPressureRealC1Representative,
    Function.comp_def,
    Complex.reCLM_apply
  ] using hReal

/-- The intrinsic `Point3` derivative of the real pressure representative is
the real part of the inverse Fourier transform of `dᵢ p̂`. -/
theorem h3RawFinPressureRealC1RepresentativeOnPoint3_spatialDerivative_fin
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : Point3) :
    spatial3.d
        (h3AxisOfFin3 i)
        (h3RawFinPressureRealC1RepresentativeOnPoint3 U V)
        x
      =
    (FourierTransformInv.fourierInv
      (h3RawFinPressureFourierCoordinateDerivative U V i)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  let ξ : H3FourierPoint3 :=
    (WithLp.toLp 2 : Point3 → H3FourierPoint3) x

  have hC1 :
      SpatialC1
        (h3RawFinPressureRealC1RepresentativeOnPoint3 U V) :=
    h3RawFinPressureRealC1RepresentativeOnPoint3_contDiff_one U V

  have hTransport :=
    h3TransportScalarField_hasLineDerivAt
      hC1
      (h3AxisOfFin3 i)
      ξ

  have hPoint :
      h3FourierToPoint3CLM ξ = x := by
    ext j
    rfl

  have hTransportFunction :
      (fun y : H3FourierPoint3 =>
        h3RawFinPressureRealC1RepresentativeOnPoint3 U V
          (h3FourierToPoint3CLM y))
        =
      h3RawFinPressureRealC1Representative U V := by
    funext y
    unfold h3RawFinPressureRealC1RepresentativeOnPoint3
    congr 1

  rw [hTransportFunction, hPoint] at hTransport

  change
    HasLineDerivAt ℝ
      (h3RawFinPressureRealC1Representative U V)
      (spatial3.d
        (h3AxisOfFin3 i)
        (h3RawFinPressureRealC1RepresentativeOnPoint3 U V)
        x)
      ξ
      (h3FourierAxisDirection (h3AxisOfFin3 i))
    at hTransport

  have hFourier :=
    h3RawFinPressureRealC1Representative_hasLineDerivAt_fin
      U V i ξ

  have hUnique := hTransport.unique hFourier

  simpa only [ξ] using hUnique

/-- The Fourier derivative of pressure is exactly the projected forcing minus
the raw forcing. -/
theorem h3RawFinPressureFourierCoordinateDerivative_eq_leray_sub_raw
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    h3RawFinPressureFourierCoordinateDerivative U V i
      =
    fun ξ : H3FourierPoint3 =>
      h3RawFinLerayOuterProductDivergence U V i ξ
        -
      h3RawFinOuterProductDivergence U V i ξ := by
  funext ξ
  unfold h3RawFinPressureFourierCoordinateDerivative
  rw [
    h3RawFinLerayOuterProductDivergence_eq_raw_add_derivative_mul_pressure
  ]
  ring

/-- Final pressure-gradient form on `Point3`: one spatial pressure derivative is
the real inverse Fourier reconstruction of the Leray forcing minus the raw
forcing. -/
theorem h3RawFinPressureRealC1RepresentativeOnPoint3_spatialDerivative_fin_eq_leray_sub_raw
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : Point3) :
    spatial3.d
        (h3AxisOfFin3 i)
        (h3RawFinPressureRealC1RepresentativeOnPoint3 U V)
        x
      =
    (FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3RawFinLerayOuterProductDivergence U V i ξ
          -
        h3RawFinOuterProductDivergence U V i ξ)
      ((WithLp.toLp 2 : Point3 → H3FourierPoint3) x)).re := by
  rw [
    h3RawFinPressureRealC1RepresentativeOnPoint3_spatialDerivative_fin
  ]
  rw [
    h3RawFinPressureFourierCoordinateDerivative_eq_leray_sub_raw
  ]

end

end Euclidean
end Bridge
end PrimeTensor
