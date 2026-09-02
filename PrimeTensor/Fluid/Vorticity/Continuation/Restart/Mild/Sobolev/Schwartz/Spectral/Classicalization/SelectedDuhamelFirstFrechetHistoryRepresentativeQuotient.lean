import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetHistoryQuotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.H3.Real.C1.FDerivCoordinate
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.HistoryHeatC1Bridge

/-!
# Classicalization: literal first-Fréchet old-history quotient

`SelectedDuhamelFirstFrechetHistoryQuotient` closed the one-sided old-history
limit in Fourier reconstruction form.  This file identifies that reconstructed
quotient with the literal normalized difference of coordinate evaluations of
the spatial Fréchet derivative.

For positive elapsed heat time `h`, the old-history representative is the
canonical `C¹` representative of the heat-evolved selected Duhamel H³ state.
The generic coordinate Fréchet formula therefore gives

    D oldHistory(h,x)[e_a]
      =
    F⁻¹[d_a · historyRaw(h)](x).

At zero elapsed time, the same generic formula and the selected-Duhamel raw
a.e. bridge give

    D Duhamel(t,x)[e_a]
      =
    F⁻¹[d_a · selectedRaw(t)](x).

Inverse-Fourier linearity then yields the exact identity

    coordinateQuotient(h,x)
      =
    h⁻¹ •
      (D oldHistory(h,x)[e_a] - D Duhamel(t,x)[e_a]).

Combining this identity with the already-compiled Fourier-side convergence
closes the literal old-history contribution needed by the first-Fréchet right
quotient.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetHistoryRepresentativeQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At positive elapsed heat time, the coordinate Fréchet derivative of the
old-history heat representative is the inverse Fourier transform of the
coordinate-multiplied explicit history raw amplitude. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_fderiv_apply_fin_eq_fourierInv
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    (fderiv ℝ
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      =
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          h3SelectedDuhamelHistoryHeatRawAmplitude
            ν A t h hν U₀ hA hU₀ ht i ξ)
      x := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk h hh.le) D

  let C : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol a ξ *
        h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ

  have hRep :
      h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i
        =
      h3SpectralScalarC1Representative H := by
    dsimp only [H, D, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_spectralScalarC1Representative_heatApplyNN
        hν U₀ hA hU₀ ht hh i

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i := by
    simpa only [D, W] using hSelected0

  have hHistoryHeat :
      h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative ν h D := by
    filter_upwards [hSelected] with ξ hξ
    unfold h3SelectedDuhamelHistoryHeatRawAmplitude
    unfold h3SpectralScalarHeatRawRepresentative
    rw [← hξ]

  have hPkg :
      h3SpectralScalarHeatRawRepresentativeL2 ν h hν hh D
        =
      h3SpectralScalarRawFourierL2 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
        hν hh D

  have hHeatL2 :=
    h3SpectralScalarHeatRawRepresentativeL2_ae hν hh D

  rw [hPkg] at hHeatL2

  have hRawL2 :
      ((h3SpectralScalarRawFourierL2 H : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    h3SpectralScalarRawFourierL2_ae H

  have hHeatRaw :
      h3SpectralScalarHeatRawRepresentative ν h D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    hHeatL2.symm.trans hRawL2

  have hHistoryRaw :
      h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    hHistoryHeat.trans hHeatRaw

  have hCoordinateAE :
      h3SpectralScalarRawFourierCoordinateDerivative H a
        =ᵐ[(volume : Measure H3FourierPoint3)]
      C := by
    filter_upwards [hHistoryRaw] with ξ hξ
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    dsimp only [C]
    rw [← hξ]

  calc
    (fderiv ℝ
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
        =
      (fderiv ℝ
        (h3SpectralScalarC1Representative H)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
          rw [hRep]
    _ =
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative H a)
        x :=
      h3SpectralScalarC1Representative_fderiv_apply_fin H a x
    _ =
      FourierTransformInv.fourierInv C x :=
      _root_.Real.fourierInv_congr_ae hCoordinateAE x
    _ =
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            h3SelectedDuhamelHistoryHeatRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ)
        x := by
          rfl

/-- At the base selected Duhamel time, the coordinate Fréchet derivative is
the inverse Fourier transform of the coordinate-multiplied explicit selected
Duhamel raw amplitude. -/
theorem h3SelectedDuhamelC1Representative_fderiv_apply_fin_eq_fourierInv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    (fderiv ℝ
        (h3SpectralScalarC1Representative D)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
      =
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ)
      x := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let C : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol a ξ *
        h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i := by
    simpa only [D, W] using hSelected0

  have hCoordinateAE :
      h3SpectralScalarRawFourierCoordinateDerivative D a
        =ᵐ[(volume : Measure H3FourierPoint3)]
      C := by
    filter_upwards [hSelected] with ξ hξ
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    dsimp only [C]
    rw [hξ]

  calc
    (fderiv ℝ
        (h3SpectralScalarC1Representative D)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a))
        =
      FourierTransformInv.fourierInv
        (h3SpectralScalarRawFourierCoordinateDerivative D a)
        x :=
      h3SpectralScalarC1Representative_fderiv_apply_fin D a x
    _ =
      FourierTransformInv.fourierInv C x :=
      _root_.Real.fourierInv_congr_ae hCoordinateAE x
    _ =
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ)
        x := by
          rfl

/-- The reconstructed coordinate old-history quotient is literally the
normalized difference of the corresponding spatial Fréchet evaluations. -/
theorem h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative_eq_inv_smul_sub_fderiv
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
        ν A t h hν U₀ hA hU₀ ht i a x
      =
    h⁻¹ •
      ((fderiv ℝ
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x) ea
        -
      (fderiv ℝ
          (h3SpectralScalarC1Representative D)
          x) ea) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let H : H3SpectralScalarState :=
    h3SpectralScalarHeatApplyNN
      ν hν.le (NNReal.mk h hh.le) D

  let CH : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol a ξ *
        h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i ξ

  let C0 : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol a ξ *
        h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ

  have hHistoryValue :
      FourierTransformInv.fourierInv CH x
        =
      (fderiv ℝ
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
    dsimp only [CH]
    exact
      (h3SelectedDuhamelHistoryHeatRepresentative_fderiv_apply_fin_eq_fourierInv
        hν U₀ hA hU₀ ht hh i a x).symm

  have hBaseValue :
      FourierTransformInv.fourierInv C0 x
        =
      (fderiv ℝ
        (h3SpectralScalarC1Representative D)
        x)
        (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
    dsimp only [C0, D, W]
    exact
      (h3SelectedDuhamelC1Representative_fderiv_apply_fin_eq_fourierInv
        hν U₀ hA hU₀ ht i a x).symm

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SelectedDuhamelRawFourierAmplitude
        ν A t hν U₀ hA hU₀ ht i := by
    simpa only [D, W] using hSelected0

  have hPkg :
      h3SpectralScalarHeatRawRepresentativeL2 ν h hν hh D
        =
      h3SpectralScalarRawFourierL2 H := by
    dsimp only [H]
    exact
      h3SpectralScalarHeatRawRepresentativeL2_eq_rawFourierL2_heatApplyNN
        hν hh D

  have hHeatL2 :=
    h3SpectralScalarHeatRawRepresentativeL2_ae hν hh D

  rw [hPkg] at hHeatL2

  have hRawL2 :
      ((h3SpectralScalarRawFourierL2 H : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    h3SpectralScalarRawFourierL2_ae H

  have hHistoryHeat :
      h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative ν h D := by
    filter_upwards [hSelected] with ξ hξ
    unfold h3SelectedDuhamelHistoryHeatRawAmplitude
    unfold h3SpectralScalarHeatRawRepresentative
    rw [← hξ]

  have hHeatRaw :
      h3SpectralScalarHeatRawRepresentative ν h D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    hHeatL2.symm.trans hRawL2

  have hHistoryRaw :
      h3SelectedDuhamelHistoryHeatRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier H :=
    hHistoryHeat.trans hHeatRaw

  have hCHAE :
      CH
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourierCoordinateDerivative H a := by
    filter_upwards [hHistoryRaw] with ξ hξ
    dsimp only [CH]
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    rw [hξ]

  have hC0AE :
      C0
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourierCoordinateDerivative D a := by
    filter_upwards [hSelected] with ξ hξ
    dsimp only [C0]
    unfold h3SpectralScalarRawFourierCoordinateDerivative
    rw [← hξ]

  have hCH :
      Integrable CH (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourierCoordinateDerivative_integrable H a).congr
      hCHAE.symm

  have hC0 :
      Integrable C0 (volume : Measure H3FourierPoint3) :=
    (h3SpectralScalarRawFourierCoordinateDerivative_integrable D a).congr
      hC0AE.symm

  have hRawEq :
      h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i a
        =
      ((((h⁻¹ : ℝ) : ℂ) • (CH - C0))) := by
    funext ξ
    unfold h3SelectedDuhamelHistoryHeatCoordinateQuotientRawAmplitude
    unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
    rw [
      h3SelectedDuhamelHistoryHeatRawAmplitude_zero
        hν U₀ hA hU₀ ht i
    ]
    dsimp only [CH, C0, Pi.sub_apply, Pi.smul_apply]
    simp [Complex.real_smul]
    <;> push_cast
    <;> ring

  have hInnerNegContinuous :
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          ((-(innerₗ H3FourierPoint3)) p.1) p.2) := by
    change
      Continuous
        (fun p : H3FourierPoint3 × H3FourierPoint3 =>
          -inner ℝ p.1 p.2)
    exact
      (continuous_inner
        (𝕜 := ℝ)
        (E := H3FourierPoint3)).neg

  have hInvNeg :
      FourierTransformInv.fourierInv (-C0) x
        =
      -FourierTransformInv.fourierInv C0 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (-C0)
          x
        =
      -VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          C0
          x

    have hSmul :=
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          C0
          (-1 : ℂ))
        x

    simpa using hSmul

  have hInvAdd :
      FourierTransformInv.fourierInv (CH + (-C0)) x
        =
      FourierTransformInv.fourierInv CH x
        +
      FourierTransformInv.fourierInv (-C0) x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (CH + (-C0))
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          CH
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (-C0)
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hCH
          hC0.neg)
        x

  have hInvSub :
      FourierTransformInv.fourierInv (CH - C0) x
        =
      FourierTransformInv.fourierInv CH x
        -
      FourierTransformInv.fourierInv C0 x := by
    rw [sub_eq_add_neg, hInvAdd, hInvNeg]
    rfl

  have hInvSmul :
      FourierTransformInv.fourierInv
          ((((h⁻¹ : ℝ) : ℂ) • (CH - C0))) x
        =
      (((((h⁻¹ : ℝ) : ℂ) •
        FourierTransformInv.fourierInv (CH - C0))) x) := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((((h⁻¹ : ℝ) : ℂ) • (CH - C0)))
          x
        =
      (((((h⁻¹ : ℝ) : ℂ) •
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (CH - C0)) x))

    exact
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (CH - C0)
          (((h⁻¹ : ℝ) : ℂ)))
        x

  unfold h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
  rw [hRawEq, hInvSmul]
  simp only [Pi.smul_apply]
  rw [hInvSub, hHistoryValue, hBaseValue]

  exact
    Complex.coe_smul
      h⁻¹
      ((fderiv ℝ
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x)
          (h3FourierAxisDirection (h3AxisOfFin3 a))
        -
      (fderiv ℝ
          (h3SpectralScalarC1Representative D)
          x)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))

/-- The literal coordinate Fréchet old-history quotient converges from the
right to the reconstructed coordinate heat generator. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_fderiv_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x) ea
            -
          (fderiv ℝ
              (h3SpectralScalarC1Representative D)
              x) ea))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i a x)) := by
  dsimp only

  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative_zero_right
      hν U₀ hA hU₀ ht htR i a x

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          ((fderiv ℝ
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x)
              (h3FourierAxisDirection (h3AxisOfFin3 a))
            -
          (fderiv ℝ
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀)
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀)
                  i))
              x)
              (h3FourierAxisDirection (h3AxisOfFin3 a))))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a x) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      (h3SelectedDuhamelHistoryHeatCoordinateQuotientRepresentative_eq_inv_smul_sub_fderiv
        hν U₀ hA hU₀ ht hh i a x).symm

  exact Tendsto.congr' hEq.symm hQ

end

end Euclidean
end Bridge
end PrimeTensor
