import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Third.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Mild.Mass

/-!
# Positive-time scalar heat fourth coordinate derivatives

The order-two mixed-time closure needs the fourth spatial heat coordinate trace

    D⁴ H(t,x)[e_a,e_b,e_k,e_k].

The project already has the full positive-time fourth Fourier moment for the
free heat representative.  This file converts that moment into an explicit
ordered fourth-coordinate inverse-Fourier representative and identifies it
with the corresponding fourth Fréchet evaluation.

No temporal differentiation and no new heat estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeFourthCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for an ordered fourth coordinate derivative of the
positive-time scalar heat reconstruction. -/
noncomputable def h3SpectralScalarHeatFourthCoordinateRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      (h3FourierDerivativeSymbol c ξ *
        (h3FourierDerivativeSymbol d ξ *
          h3SpectralScalarHeatRawRepresentative ν t G ξ)))

/-- The four project coordinate symbols are Mathlib's order-four
inverse-Fourier multiplier on the corresponding canonical directions. -/
theorem h3SpectralScalarHeatFourthCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let ec : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 c)
    let ed : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 d)
    let m : Fin 4 → H3FourierPoint3 :=
      ![ea, eb, ec, ed]
    VectorFourier.fourierPowSMulRight
        L
        (h3SpectralScalarHeatRawRepresentative ν t G)
        ξ
        4
        m
      =
    h3SpectralScalarHeatFourthCoordinateRawAmplitude
      ν t G a b c d ξ := by
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

  unfold h3SpectralScalarHeatFourthCoordinateRawAmplitude
  rw [ha, hb, hc, hd]
  dsimp only [ea, eb, ec, ed]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- Four canonical coordinate symbols cost at most the full radial fourth heat
moment. -/
theorem norm_h3SpectralScalarHeatFourthCoordinateRawAmplitude_le_fourthMoment
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatFourthCoordinateRawAmplitude
        ν t G a b c d ξ‖
      ≤
    (2 * Real.pi) ^ 4 *
      (‖ξ‖ ^ 4 *
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖) := by
  unfold h3SpectralScalarHeatFourthCoordinateRawAmplitude
  rw [norm_mul, norm_mul, norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ
  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ
  have hc :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude c ξ
  have hd :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude d ξ

  have hH :
      0 ≤
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)))
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg
            (norm_nonneg _)
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hH)))
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (‖h3FourierDerivativeSymbol c ξ‖ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            hb
            (mul_nonneg
              (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) hH)))
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          (h3FourierGradientMagnitude ξ *
            (‖h3FourierDerivativeSymbol d ξ‖ *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              hc
              (mul_nonneg (norm_nonneg _) hH))
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
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hd hH)
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
          ‖h3SpectralScalarHeatRawRepresentative
            ν t G ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- Every ordered fourth-coordinate raw heat amplitude is integrable at
positive heat time. -/
theorem h3SpectralScalarHeatFourthCoordinateRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3) :
    Integrable
      (h3SpectralScalarHeatFourthCoordinateRawAmplitude
        ν t G a b c d)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3SpectralScalarHeatFourthCoordinateRawAmplitude
          ν t G a b c d)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SpectralScalarHeatFourthCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous c).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous d).aestronglyMeasurable.mul
              (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
                ν t G))))

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
      hν ht G

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 4 *
            (‖ξ‖ ^ 4 *
              ‖h3SpectralScalarHeatRawRepresentative
                ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 4)

  refine hMajorantInt.mono' hTargetMeas ?_

  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SpectralScalarHeatFourthCoordinateRawAmplitude_le_fourthMoment
      ν t G a b c d ξ

/-- Inverse-Fourier reconstruction of one ordered fourth-coordinate heat
amplitude. -/
noncomputable def h3SpectralScalarHeatFourthCoordinateRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatFourthCoordinateRawAmplitude
      ν t G a b c d)

/-- At positive heat time, the named fourth-coordinate reconstruction is
exactly the fourth Fréchet derivative of the scalar heat reconstruction
evaluated on the corresponding ordered coordinate directions. -/
theorem h3SpectralScalarHeatFourthCoordinateRepresentative_eq_iteratedFDeriv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b c d : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatFourthCoordinateRepresentative
        ν t G a b c d x
      =
    iteratedFDeriv ℝ 4
      (h3SpectralScalarHeatC3Representative ν t G)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b),
        h3FourierAxisDirection (h3AxisOfFin3 c),
        h3FourierAxisDirection (h3AxisOfFin3 d)
      ] := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

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

  have hMom :
      ∀ (n : ℕ), n ≤ (4 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn

    have hn4 : n ≤ 4 := by
      exact_mod_cast hn

    by_cases hn3 : n ≤ 3
    · dsimp only [f]
      exact
        h3SpectralScalarHeatRawRepresentative_moment_integrable
          hν ht G n hn3
    · have hnEq : n = 4 := by
        omega
      subst n
      dsimp only [f]
      exact
        h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
          hν ht G

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G

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
      h3SpectralScalarHeatFourthCoordinateRawAmplitude
        ν t G a b c d := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SpectralScalarHeatFourthCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν t G a b c d ξ

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

  have hInner :
      ContinuousLinearMap.toLinearMap₁₂
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
        =
      -(innerₗ H3FourierPoint3) := by
    ext v w
    simp only [
      ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
      neg_apply,
      innerSL_apply_apply,
      LinearMap.neg_apply,
      innerₗ_apply_apply
    ]

  dsimp only [L] at hEval
  rw [hInner] at hEval

  unfold
    h3SpectralScalarHeatFourthCoordinateRepresentative
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SpectralScalarHeatFourthCoordinateRawAmplitude
          ν t G a b c d)
        x
      =
    iteratedFDeriv ℝ 4
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x m

  simpa only [m] using hEval.symm

end

end Euclidean
end Bridge
end PrimeTensor
