import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Third.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Raw.Fourth.Moment

/-!
# Classicalization: selected Duhamel fourth-coordinate reconstruction

The order-two old-history generator trace requires the genuine fourth spatial
Fréchet derivative of the selected Duhamel reconstruction.

For canonical coordinates `a,b,c,d`, define the raw multiplier

    d_a(ξ) d_b(ξ) d_c(ξ) d_d(ξ) A_t(ξ),

where `A_t` is the named selected Duhamel raw Fourier amplitude.

The selected Duhamel branch already supplies all radial moments through order
four.  Mathlib's inverse-Fourier differentiability theorem therefore identifies
the inverse Fourier transform of this multiplier with

    D⁴ Duhamel(t,x)[e_a,e_b,e_c,e_d].

No temporal differentiation and no new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFourthCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for one ordered fourth spatial coordinate derivative
of the named selected Duhamel reconstruction. -/
noncomputable def h3SelectedDuhamelFourthCoordinateRawAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c d : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      (h3FourierDerivativeSymbol c ξ *
        (h3FourierDerivativeSymbol d ξ *
          h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ)))

/-- The four selected-Duhamel coordinate symbols are exactly Mathlib's
order-four inverse-Fourier multiplier on the corresponding canonical
directions. -/
theorem h3SelectedDuhamelFourthCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c d : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let m : Fin 4 → H3FourierPoint3 :=
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d)
      ]
    VectorFourier.fourierPowSMulRight
        L
        (h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i)
        ξ
        4
        m
      =
    h3SelectedDuhamelFourthCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a b c d ξ := by
  dsimp only

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)
  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)
  let ec : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 c)
  let ed : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 d)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hb :
      h3FourierDerivativeSymbol b ξ
        =
      ((2 * Real.pi * inner ℝ ξ eb : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [eb]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hc :
      h3FourierDerivativeSymbol c ξ
        =
      ((2 * Real.pi * inner ℝ ξ ec : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ec]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  have hd :
      h3FourierDerivativeSymbol d ξ
        =
      ((2 * Real.pi * inner ℝ ξ ed : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ed]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_four,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SelectedDuhamelFourthCoordinateRawAmplitude
  rw [ha, hb, hc, hd]
  dsimp only [ea, eb, ec, ed]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- Four selected-Duhamel coordinate symbols cost at most the radial fourth
moment. -/
theorem norm_h3SelectedDuhamelFourthCoordinateRawAmplitude_le_fourthMoment
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i a b c d : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SelectedDuhamelFourthCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c d ξ‖
      ≤
    (2 * Real.pi) ^ 4 *
      (‖ξ‖ ^ 4 *
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖) := by
  unfold h3SelectedDuhamelFourthCoordinateRawAmplitude
  rw [norm_mul, norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ
  have hd :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude d ξ

  have hAmp :
      0 ≤
        ‖h3SelectedDuhamelRawFourierAmplitude
          ν A t hν U₀ hA hU₀ ht i ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖)))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hAmp)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hAmp)))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hc
              (mul_nonneg (norm_nonneg _) hAmp))
            (by
              unfold h3FourierGradientMagnitude
              positivity))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (h3FourierGradientMagnitude ξ *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hd hAmp)
              (by
                unfold h3FourierGradientMagnitude
                positivity))
            (by
              unfold h3FourierGradientMagnitude
              positivity))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (2 * Real.pi) ^ 4 *
        (‖ξ‖ ^ 4 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- Every ordered fourth-coordinate selected-Duhamel raw amplitude is
integrable in the strict positive restart interval. -/
theorem h3SelectedDuhamelFourthCoordinateRawAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d : Fin 3) :
    Integrable
      (h3SelectedDuhamelFourthCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c d)
      (volume : Measure H3FourierPoint3) := by
  have hAmpInt :=
    h3SelectedDuhamelRawFourierAmplitude_integrable
      hν U₀ hA hU₀ ht i

  have hMeas :
      AEStronglyMeasurable
        (h3SelectedDuhamelFourthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SelectedDuhamelFourthCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous d).aestronglyMeasurable.mul
              hAmpInt.aestronglyMeasurable)))

  have hMoment :=
    h3SelectedDuhamelRawFourierAmplitude_fourthMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 4 *
            (‖ξ‖ ^ 4 *
              ‖h3SelectedDuhamelRawFourierAmplitude
                ν A t hν U₀ hA hU₀ ht i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul ((2 * Real.pi) ^ 4)

  refine hScaled.mono' hMeas ?_
  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SelectedDuhamelFourthCoordinateRawAmplitude_le_fourthMoment
      ν A t hν U₀ hA hU₀ ht i a b c d ξ

/-- One selected-Duhamel fourth-coordinate raw amplitude reconstructs exactly
the evaluated fourth Fréchet derivative of the named selected-Duhamel
inverse-Fourier representative. -/
theorem h3SelectedDuhamelFourthCoordinateRepresentative_eq_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d : Fin 3)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelFourthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d)
        x
      =
    iteratedFDeriv ℝ 4
      (h3SelectedDuhamelC1Representative
        ν A t hν U₀ hA hU₀ ht i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d)
      ] := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel ν t hν W W i

  let f : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 4 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d)
    ]

  have hSelected0 :=
    h3SpectralScalarRawFourier_selectedDuhamel_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hSelected :
      h3SpectralScalarRawFourier D
        =ᵐ[(volume : Measure H3FourierPoint3)]
      f := by
    dsimp only [D, W, f]
    simpa only [W] using hSelected0

  have hAmpInt :
      Integrable f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_integrable
        hν U₀ hA hU₀ ht i

  have hFirstD :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖h3SpectralScalarRawFourier D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarRawFourier_firstMoment_integrable D

  have hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    refine hFirstD.congr ?_
    filter_upwards [hSelected] with ξ hξ
    rw [hξ]

  have hSecond :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hThird :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_thirdMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFourth :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SelectedDuhamelRawFourierAmplitude_fourthMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMom :
      ∀ (n : ℕ), n ≤ (4 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn4 : n ≤ 4 := by
      exact_mod_cast hn
    have hnCases :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl | rfl
    · simpa only [pow_zero, one_mul] using hAmpInt.norm
    · simpa only [pow_one] using hFirst
    · exact hSecond
    · exact hThird
    · exact hFourth

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) :=
    hAmpInt.aestronglyMeasurable

  have hDeriv :=
    VectorFourier.iteratedFDeriv_fourierIntegral
      (L := L)
      (f := f)
      (μ := (volume : Measure H3FourierPoint3))
      hMom
      hMeas
      (n := 4)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 4 m)
        =
      h3SelectedDuhamelFourthCoordinateRawAmplitude
        ν A t hν U₀ hA hU₀ ht i a b c d := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SelectedDuhamelFourthCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν A t hν U₀ hA hU₀ ht i a b c d ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 4)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 4 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval
  rw [hRawEq] at hEval

  unfold h3SelectedDuhamelC1Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SelectedDuhamelFourthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d)
        x
      =
    iteratedFDeriv ℝ 4
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x
      m

  exact hEval.symm

/-- The same fourth-coordinate reconstruction is the genuine fourth Fréchet
derivative of the literal selected classical Duhamel integral. -/
theorem h3SelectedDuhamelFourthCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a b c d : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    FourierTransformInv.fourierInv
        (h3SelectedDuhamelFourthCoordinateRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a b c d)
        x
      =
    iteratedFDeriv ℝ 4
      (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
        ν t W W i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d)
      ] := by
  dsimp only

  have hFourth :=
    h3SelectedDuhamelFourthCoordinateRepresentative_eq_iteratedFDeriv
      hν U₀ hA hU₀ ht htR i a b c d x

  have hFull :=
    h3SelectedDuhamelC1Representative_eq_C3Duhamel
      hν U₀ hA hU₀ ht htR i

  dsimp only at hFull
  rw [hFull] at hFourth
  exact hFourth

end

end Euclidean
end Bridge
end PrimeTensor
