import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Hessian.Trace.Representative

/-!
# Positive-time scalar heat mixed second coordinate derivative

The order-two selected mixed-time frontier needs the full mixed Hessian of the
positive-time heat reconstruction, not only the three diagonal entries used by
the Laplacian trace.

For canonical coordinate directions `a,b`, define the raw Fourier amplitude

    D_a(ξ) D_b(ξ) heatRaw(ν,t,G,ξ).

Two derivative symbols cost at most `(2π)^2 |ξ|^2`, so the existing
positive-time second heat moment makes this amplitude integrable.  Mathlib's
order-two Fourier differentiability theorem then identifies its inverse-Fourier
reconstruction exactly with

    D² heat(t,x)[e_a,e_b].

No temporal derivative or new heat estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeSecondCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for an ordered pair of canonical coordinate
derivatives of the positive-time scalar heat reconstruction. -/
noncomputable def h3SpectralScalarHeatSecondCoordinateRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      h3SpectralScalarHeatRawRepresentative ν t G ξ)

/-- The ordered pair of project derivative symbols is exactly Mathlib's
order-two inverse-Fourier multiplier on the corresponding canonical
directions. -/
theorem h3SpectralScalarHeatSecondCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let eb : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 b)
    let m : Fin 2 → H3FourierPoint3 :=
      ![ea, eb]
    VectorFourier.fourierPowSMulRight
        L
        (h3SpectralScalarHeatRawRepresentative ν t G)
        ξ
        2
        m
      =
    h3SpectralScalarHeatSecondCoordinateRawAmplitude
      ν t G a b ξ := by
  dsimp only

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

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

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    Fin.prod_univ_two,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SpectralScalarHeatSecondCoordinateRawAmplitude
  rw [ha, hb]
  dsimp only [ea, eb]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Two canonical coordinate derivatives cost at most the radial second heat
moment. -/
theorem norm_h3SpectralScalarHeatSecondCoordinateRawAmplitude_le_secondMoment
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatSecondCoordinateRawAmplitude
        ν t G a b ξ‖
      ≤
    (2 * Real.pi) ^ 2 *
      (‖ξ‖ ^ 2 *
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖) := by
  unfold h3SpectralScalarHeatSecondCoordinateRawAmplitude
  rw [norm_mul, norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  have hb :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

  have hHeat :
      0 ≤
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖ :=
    norm_nonneg _

  have hInner :
      ‖h3FourierDerivativeSymbol b ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
        ≤
      h3FourierGradientMagnitude ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ :=
    mul_le_mul_of_nonneg_right hb hHeat

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol b ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          ha
          (mul_nonneg (norm_nonneg _) hHeat)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          hInner
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (2 * Real.pi) ^ 2 *
        (‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- The mixed second-coordinate raw heat amplitude is integrable at every
positive heat time. -/
theorem h3SpectralScalarHeatSecondCoordinateRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b : Fin 3) :
    Integrable
      (h3SpectralScalarHeatSecondCoordinateRawAmplitude
        ν t G a b)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3SpectralScalarHeatSecondCoordinateRawAmplitude
          ν t G a b)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SpectralScalarHeatSecondCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
          (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
            ν t G))

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G 2 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖h3SpectralScalarHeatRawRepresentative
                ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 2)

  refine hMajorantInt.mono' hTargetMeas ?_

  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SpectralScalarHeatSecondCoordinateRawAmplitude_le_secondMoment
      ν t G a b ξ

/-- Inverse-Fourier reconstruction of an ordered mixed second-coordinate heat
amplitude. -/
noncomputable def h3SpectralScalarHeatSecondCoordinateRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatSecondCoordinateRawAmplitude
      ν t G a b)

/-- At positive heat time, the named mixed second-coordinate reconstruction is
exactly the second spatial Fréchet derivative of the scalar heat
reconstruction evaluated on the corresponding ordered canonical directions. -/
theorem h3SpectralScalarHeatSecondCoordinateRepresentative_eq_iteratedFDeriv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatSecondCoordinateRepresentative
        ν t G a b x
      =
    iteratedFDeriv ℝ 2
      (h3SpectralScalarHeatC3Representative ν t G)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ] := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let eb : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 b)

  let m : Fin 2 → H3FourierPoint3 :=
    ![ea, eb]

  have hMom :
      ∀ (n : ℕ), n ≤ (2 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn2 : n ≤ 2 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G n (hn2.trans (by norm_num))

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
      (n := 2)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 2 m)
        =
      h3SpectralScalarHeatSecondCoordinateRawAmplitude
        ν t G a b := by
    funext ξ
    dsimp only [L, f, m, ea, eb]
    exact
      h3SpectralScalarHeatSecondCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν t G a b ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 2)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 2 (by norm_num))
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
    h3SpectralScalarHeatSecondCoordinateRepresentative
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SpectralScalarHeatSecondCoordinateRawAmplitude
          ν t G a b)
        x
      =
    iteratedFDeriv ℝ 2
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x m

  simpa only [m, ea, eb] using hEval.symm

end

end Euclidean
end Bridge
end PrimeTensor
