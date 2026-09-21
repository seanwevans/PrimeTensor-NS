import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Frechet.History.Quotient
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pointwise.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Third.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.History.Heat.C1.Bridge

/-!
# Classicalization: literal third-Fréchet old-history quotient

The order-three old-history quotient now converges after inverse-Fourier
reconstruction.  This file identifies that reconstructed quotient with the
literal normalized difference of third spatial Fréchet coordinate
evaluations.

For positive elapsed heat time `h`,

    D³ oldHistory(h,x)[e_a,e_b,e_c]
      =
    F⁻¹[d_a d_b d_c historyRaw(h)](x),

while at the base selected Duhamel time

    D³ Duhamel(t,x)[e_a,e_b,e_c]
      =
    F⁻¹[d_a d_b d_c selectedRaw(t)](x).

Inverse-Fourier linearity then gives the exact literal quotient identity.
Combining it with the already-closed Fourier-side limit transports the
old-history convergence to the actual third Fréchet coordinate.

No temporal estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelThirdFrechetHistoryRepresentativeQuotient
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At positive elapsed heat time, the ordered third Fréchet coordinate of
the literal old-history heat representative is the inverse Fourier transform
of the three-coordinate-multiplied explicit history raw amplitude. -/
theorem h3SelectedDuhamelHistoryHeatRepresentative_thirdFrechet_eval_fin_eq_fourierInv
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (hh : 0 < h)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    iteratedFDeriv ℝ 3
      (h3SelectedDuhamelHistoryHeatRepresentative
        ν A t h hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
      =
    FourierTransformInv.fourierInv
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          (h3FourierDerivativeSymbol b ξ *
            (h3FourierDerivativeSymbol c ξ *
              h3SelectedDuhamelHistoryHeatRawAmplitude
                ν A t h hν U₀ hA hU₀ ht i ξ)))
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
          (h3FourierDerivativeSymbol c ξ *
            h3SelectedDuhamelHistoryHeatRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ))

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
      h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν h D a b c
        =ᵐ[(volume : Measure H3FourierPoint3)]
      C := by
    filter_upwards [hHistoryHeat] with ξ hξ
    unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
    dsimp only [C]
    rw [← hξ]

  have hHeatCoordinate :=
    h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν hh D a b c x

  calc
    iteratedFDeriv ℝ 3
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c)
        ]
        =
      iteratedFDeriv ℝ 3
        (h3SpectralScalarHeatC3Representative ν h D)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c)
        ] := by
          rw [hRep, hHeatRep]
    _ =
      h3SpectralScalarHeatThirdCoordinateRepresentative
        ν h D a b c x := by
          exact hHeatCoordinate.symm
    _ =
      FourierTransformInv.fourierInv C x := by
          unfold h3SpectralScalarHeatThirdCoordinateRepresentative
          exact
            _root_.Real.fourierInv_congr_ae
              hCoordinateAE
              x
    _ =
      FourierTransformInv.fourierInv
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            (h3FourierDerivativeSymbol b ξ *
              (h3FourierDerivativeSymbol c ξ *
                h3SelectedDuhamelHistoryHeatRawAmplitude
                  ν A t h hν U₀ hA hU₀ ht i ξ)))
        x := by
          rfl

/-- At the base selected Duhamel time, the ordered third Fréchet coordinate
is the inverse Fourier transform of the three-coordinate-multiplied explicit
selected-Duhamel raw amplitude. -/
theorem h3SelectedDuhamelC1Representative_thirdFrechet_eval_fin_eq_fourierInv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    iteratedFDeriv ℝ 3
      (h3SpectralScalarC1Representative D)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
      =
    FourierTransformInv.fourierInv
      (h3SelectedDuhamelThirdCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c)
      x := by
  dsimp only

  have hThird :=
    h3SelectedDuhamelThirdCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b c x

  have hGeneric :=
    h3SelectedDuhamelC1Representative_eq_spectralScalarC1Representative
      hν U₀ hA hU₀ ht i

  dsimp only at hGeneric
  rw [hGeneric] at hThird
  exact hThird.symm

/-- The reconstructed third-coordinate old-history quotient is literally the
normalized difference of the corresponding third spatial Fréchet
evaluations. -/
theorem h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative_eq_inv_smul_sub_thirdFrechet
    {ν A t h : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hh : 0 < h)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
    h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
        ν A t h hν U₀ hA hU₀ ht i a b c x
      =
    h⁻¹ •
      (iteratedFDeriv ℝ 3
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x m
        -
       iteratedFDeriv ℝ 3
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
          (h3FourierDerivativeSymbol c ξ *
            h3SelectedDuhamelHistoryHeatRawAmplitude
              ν A t h hν U₀ hA hU₀ ht i ξ))

  let C0 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelThirdCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b c

  have hHistoryValue :
      FourierTransformInv.fourierInv CH x
        =
      iteratedFDeriv ℝ 3
        (h3SelectedDuhamelHistoryHeatRepresentative
          ν A t h hν U₀ hA hU₀ ht i)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c)
        ] := by
    dsimp only [CH]
    exact
      (h3SelectedDuhamelHistoryHeatRepresentative_thirdFrechet_eval_fin_eq_fourierInv
        hν U₀ hA hU₀ ht hh i a b c x).symm

  have hBaseValue :
      FourierTransformInv.fourierInv C0 x
        =
      iteratedFDeriv ℝ 3
        (h3SpectralScalarC1Representative D)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 a),
          h3FourierAxisDirection (h3AxisOfFin3 b),
          h3FourierAxisDirection (h3AxisOfFin3 c)
        ] := by
    dsimp only [C0, D, W]
    exact
      (h3SelectedDuhamelC1Representative_thirdFrechet_eval_fin_eq_fourierInv
        hν U₀ hA hU₀ ht htR i a b c x).symm

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
      h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν h D a b c
        =ᵐ[(volume : Measure H3FourierPoint3)]
      CH := by
    filter_upwards [hHistoryHeat] with ξ hξ
    unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
    dsimp only [CH]
    rw [← hξ]

  have hCH :
      Integrable CH
        (volume : Measure H3FourierPoint3) := by
    exact
      (h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
        hν hh D a b c).congr hCHAE

  have hC0 :
      Integrable C0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [C0]
    exact
      h3SelectedDuhamelThirdCoordinateRawAmplitude_integrable
        hν U₀ hA hU₀ ht htR i a b c

  have hRawEq :
      h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
          ν A t h hν U₀ hA hU₀ ht i a b c
        =
      ((((h⁻¹ : ℝ) : ℂ) • (CH - C0))) := by
    funext ξ
    unfold h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRawAmplitude
    unfold h3SelectedDuhamelHistoryHeatQuotientRawAmplitude
    rw [
      h3SelectedDuhamelHistoryHeatRawAmplitude_zero
        hν U₀ hA hU₀ ht i
    ]
    dsimp only [
      CH,
      C0,
      h3SelectedDuhamelThirdCoordinateRawAmplitude,
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

  unfold h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
  rw [hRawEq, hInvSmul]
  simp only [Pi.smul_apply]
  rw [hInvSub, hHistoryValue, hBaseValue]

  exact
    Complex.coe_smul
      h⁻¹
      (iteratedFDeriv ℝ 3
          (h3SelectedDuhamelHistoryHeatRepresentative
            ν A t h hν U₀ hA hU₀ ht i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c)
          ]
        -
       iteratedFDeriv ℝ 3
          (h3SpectralScalarC1Representative D)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c)
          ])

/-- The literal third-Fréchet old-history quotient converges from the right
to the reconstructed third-coordinate heat generator. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_thirdFrechet_coordinate_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3SpectralScalarState :=
      h3SpectralFinHeatLerayDuhamel ν t hν W W i
    let m : Fin 3 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c)
      ]
    Tendsto
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 3
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x m
            -
           iteratedFDeriv ℝ 3
              (h3SpectralScalarC1Representative D)
              x m))
      (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝
        (h3SelectedDuhamelHistoryHeatThirdCoordinateGeneratorRepresentative
          ν A t hν U₀ hA hU₀ ht i a b c x)) := by
  dsimp only

  have hQ :=
    tendsto_h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative_zero_right
      hν U₀ hA hU₀ ht htR i a b c x

  have hEq :
      (fun h : ℝ =>
        h⁻¹ •
          (iteratedFDeriv ℝ 3
              (h3SelectedDuhamelHistoryHeatRepresentative
                ν A t h hν U₀ hA hU₀ ht i)
              x
              ![
                h3FourierAxisDirection (h3AxisOfFin3 a),
                h3FourierAxisDirection (h3AxisOfFin3 b),
                h3FourierAxisDirection (h3AxisOfFin3 c)
              ]
            -
           iteratedFDeriv ℝ 3
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
                h3FourierAxisDirection (h3AxisOfFin3 b),
                h3FourierAxisDirection (h3AxisOfFin3 c)
              ]))
        =ᶠ[𝓝[Set.Ioi (0 : ℝ)] 0]
      (fun h : ℝ =>
        h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative
          ν A t h hν U₀ hA hU₀ ht i a b c x) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact
      (h3SelectedDuhamelHistoryHeatThirdCoordinateQuotientRepresentative_eq_inv_smul_sub_thirdFrechet
        hν U₀ hA hU₀ ht htR hh i a b c x).symm

  exact Tendsto.congr' hEq.symm hQ

end

end Euclidean
end Bridge
end PrimeTensor
