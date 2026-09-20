import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.History.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pointwise.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Second.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.History.Heat.C1.Bridge

/-!
# Classicalization: literal second-Fréchet old-history quotient

The order-two old-history quotient now converges after inverse-Fourier
reconstruction.  This file identifies that reconstructed quotient with the
literal normalized difference of second spatial Fréchet coordinate
evaluations.

For positive elapsed heat time `h`,

    D² oldHistory(h,x)[e_a,e_b]
      =
    F⁻¹[d_a d_b historyRaw(h)](x),

while at the base selected Duhamel time

    D² Duhamel(t,x)[e_a,e_b]
      =
    F⁻¹[d_a d_b selectedRaw(t)](x).

Inverse-Fourier linearity then gives the exact literal quotient identity.
Combining it with the already-closed Fourier-side limit transports the
old-history convergence to the actual second Fréchet coordinate.

No temporal estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetHistoryRepresentativeQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Two selected-Duhamel coordinate symbols are controlled by the radial
second Fourier moment. -/
theorem norm_h3SelectedDuhamelSecondCoordinateRawAmplitude_le_secondMoment
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelSecondCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b ξ‖
      ≤
    (2 * Real.pi) ^ 2 *
      (‖ξ‖ ^ 2 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  unfold h3SelectedDuhamelSecondCoordinateRawAmplitude
  rw [norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

  have hAmp :
      0 ≤
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg (norm_nonneg _) hAmp)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb hAmp)
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (2 * Real.pi) ^ 2 *
        (‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- The named selected-Duhamel second-coordinate raw amplitude is integrable
throughout the strict positive restart interval. -/
theorem h3SelectedDuhamelSecondCoordinateRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3) :
    Integrable
      (h3SelectedDuhamelSecondCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b)
      (volume : Measure H3FourierPoint3) := by
  have hAmpInt :=
    h3SelectedDuhamelRawFourierAmplitude_integrable
      hν U₀ hA hU₀ ht i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelSecondCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelSecondCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          hAmpInt.aestronglyMeasurable)

  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul ((2 * Real.pi) ^ 2)

  refine hScaled.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SelectedDuhamelSecondCoordinateRawAmplitude_le_secondMoment
      ν A t hν U₀ hA hU₀ ht i a b ξ

/-- At positive elapsed heat time, the ordered second Fréchet coordinate of
the literal old-history heat representative is the inverse Fourier transform
of the twice-coordinate-multiplied explicit history raw amplitude. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_secondFrechet_eval_fin_eq_fourierInv
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    iteratedFDeriv ℝ 2
      (h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
      =
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3SelectedDuhamelHistoryHeatRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ))
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
        (h3FourierDerivativeSymbol b ξ *
          h3SelectedDuhamelHistoryHeatRawAmplitude
            ν A t h hν U₀ hA hU₀ ht i ξ)

  have hRep :
      h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i
        =
      h3SpectralScalarC1Representative H := by
    dsimp only [H, D, W]
    exact
      h3SelectedDuhamelHistoryHeatRepresentative_eq_spectralScalarC1Representative_heatApplyNN
        hν U₀ hA hU₀ ht hh i

  have hHeatRep :
      h3SpectralScalarC1Representative H
        =
      h3SpectralScalarHeatC3Representative ν h D := by
    dsimp only [H]
    exact
      h3SpectralScalarC1Representative_heatApplyNN_eq_heatC3Representative
        hν hh D

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

  have hCoordinateAE :
      h3SpectralScalarHeatSecondCoordinateRawAmplitude
          ν h D a b
        =ᵐ[(volume : Measure H3FourierPoint3)]
      C := by
    filter_upwards [hHistoryHeat] with ξ hξ
    unfold h3SpectralScalarHeatSecondCoordinateRawAmplitude
    dsimp only [C]
    rw [← hξ]

  have hHeatCoordinate :=
    h3SpectralScalarHeatSecondCoordinateRepresentative_eq_iteratedFDeriv
      hν hh D a b x

  calc
    iteratedFDeriv ℝ 2
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b)
        ]
        =
      iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative ν h D)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b)
        ] := by
          rw [hRep, hHeatRep]
    _ =
      h3SpectralScalarHeatSecondCoordinateRepresentative
        ν h D a b x := by
          exact hHeatCoordinate.symm
    _ =
      FourierTransformInv.fourierInv C x := by
          unfold h3SpectralScalarHeatSecondCoordinateRepresentative
          exact
            _root_.Real.fourierInv_congr_ae
              hCoordinateAE
              x
    _ =
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              h3SelectedDuhamelHistoryHeatRawAmplitude
                ν A t h hν U₀ hA hU₀ ht i ξ))
        x := by
          rfl

/-- At the base selected Duhamel time, the ordered second Fréchet coordinate
is the inverse Fourier transform of the twice-coordinate-multiplied explicit
selected-Duhamel raw amplitude. -/
theorem h3SelectedDuhamelC1Representative_secondFrechet_eval_fin_eq_fourierInv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    iteratedFDeriv ℝ 2
      (h3SpectralScalarC1Representative D)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
      =
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            h3SelectedDuhamelRawFourierAmplitude
              ν A t hν U₀ hA hU₀ ht i ξ))
      x := by
  dsimp only

  have hSecond :=
    h3SelectedDuhamelSecondCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b x

  have hGeneric :=
    h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
      hν U₀ hA hU₀ ht i

  dsimp only at hGeneric
  rw [hGeneric] at hSecond
  unfold h3SelectedDuhamelSecondCoordinateRawAmplitude at hSecond
  exact hSecond.symm

/-- The reconstructed second-coordinate old-history quotient is literally the
normalized difference of the corresponding second spatial Fréchet
evaluations. -/
theorem h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative_eq_inv_smul_sub_secondFrechet
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hh : 0 < h)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let m : Fin 2 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
    h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative
        ν A t h hν U₀ hA hU₀ ht i a b x
      =
    h⁻¹ •
      (iteratedFDeriv ℝ 2
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x m
        -
       iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative D)
          x m) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let CH : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3FourierDerivativeSymbol a ξ *
        (h3FourierDerivativeSymbol b ξ *
          h3SelectedDuhamelHistoryHeatRawAmplitude
            ν A t h hν U₀ hA hU₀ ht i ξ)

  let C0 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelSecondCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b

  have hHistoryValue :
      FourierTransformInv.fourierInv CH x
        =
      iteratedFDeriv ℝ 2
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b)
        ] := by
    dsimp only [CH]
    exact
      (h3SelectedDuhamelHistoryHeatRepresentative_secondFrechet_eval_fin_eq_fourierInv
        hν U₀ hA hU₀ ht hh i a b x).symm

  have hBaseValue :
      FourierTransformInv.fourierInv C0 x
        =
      iteratedFDeriv ℝ 2
        (h3SpectralScalarC1Representative D)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b)
        ] := by
    dsimp only [C0, D, W]
    exact
      (h3SelectedDuhamelC1Representative_secondFrechet_eval_fin_eq_fourierInv
        hν U₀ hA hU₀ ht htR i a b x).symm

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

  have hCHAE :
      h3SpectralScalarHeatSecondCoordinateRawAmplitude
          ν h D a b
        =ᵐ[(volume : Measure H3FourierPoint3)]
      CH := by
    filter_upwards [hHistoryHeat] with ξ hξ
    unfold h3SpectralScalarHeatSecondCoordinateRawAmplitude
    dsimp only [CH]
    rw [← hξ]

  have hCH :
      Integrable CH
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3SpectralScalarHeatSecondCoordinateRawAmplitude_integrable
        hν hh D a b).congr hCHAE

  have hC0 :
      Integrable C0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [C0]
    exact
      h3SelectedDuhamelSecondCoordinateRawAmplitude_integrable
        hν U₀ hA hU₀ ht htR i a b

  have hRawEq :
      h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i a b
        =
      ((((h⁻¹ : ℝ) : ℂ) • (CH - C0))) := by
    funext ξ
    unfold h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRawAmplitude
    unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
    rw [
      h3SelectedDuhamelHistoryHeatRawAmplitude_zero
        hν U₀ hA hU₀ ht i
    ]
    dsimp only [
      CH,
      C0,
      h3SelectedDuhamelSecondCoordinateRawAmplitude,
      Pi.sub_apply,
      Pi.smul_apply
    ]
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

  unfold h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative
  rw [hRawEq, hInvSmul]
  simp only [Pi.smul_apply]
  rw [hInvSub, hHistoryValue, hBaseValue]

  exact
    Complex.coe_smul
      h⁻¹
      (iteratedFDeriv ℝ 2
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
          ]
        -
       iteratedFDeriv ℝ 2
          (h3SpectralScalarC1Representative D)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
          ])

/-- The literal second-Fréchet old-history quotient converges from the right
to the reconstructed second-coordinate heat generator. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_secondFrechet_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let m : Fin 2 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 2
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x m
            -
           iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative D)
              x m))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatSecondCoordinateGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i a b x)) := by
  dsimp only

  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative_zero_right
      hν U₀ hA hU₀ ht htR i a b x

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 2
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b)
              ]
            -
           iteratedFDeriv ℝ 2
              (h3SpectralScalarC1Representative
                (h3SpectralFinHeatLerayDuhamel
                  ν t hν
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀)
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                    hν U₀ hA hU₀)
                  i))
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b)
              ]))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a b x) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      (h3SelectedDuhamelHistoryHeatSecondCoordinateQuotientRepresentative_eq_inv_smul_sub_secondFrechet
        hν U₀ hA hU₀ ht htR hh i a b x).symm

  exact Tendsto.congr' hEq.symm hQ

end

end Euclidean
end Bridge
end PrimeTensor
