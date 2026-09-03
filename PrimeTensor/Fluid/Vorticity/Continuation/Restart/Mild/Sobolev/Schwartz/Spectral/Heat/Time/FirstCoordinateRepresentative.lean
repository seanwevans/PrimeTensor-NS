import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.ThirdCoordinateRepresentative

/-!
# Positive-time scalar heat first coordinate derivative

The mixed-time closure needs to differentiate in time the first spatial
Fréchet derivative of the positive-time heat reconstruction.  Before taking
that time derivative, this file isolates the exact spatial Fourier
representative.

For a canonical coordinate direction `a`, define the raw amplitude

    D_a(ξ) heatRaw(ν,t,G,ξ).

One derivative symbol costs at most `2π |ξ|`, so the existing positive-time
first-moment smoothing theorem makes this amplitude integrable.  Mathlib's
explicit order-one Fourier derivative formula then identifies its inverse
Fourier reconstruction exactly with

    D heat(t,x)[e_a].

No temporal differentiation or new estimate is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeFirstCoordinateRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for one canonical coordinate derivative of the
positive-time scalar heat reconstruction. -/
noncomputable def h3SpectralScalarHeatFirstCoordinateRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    h3SpectralScalarHeatRawRepresentative ν t G ξ

/-- The project's coordinate derivative symbol is exactly Mathlib's
order-one inverse-Fourier multiplier on the corresponding canonical
coordinate direction. -/
theorem h3SpectralScalarHeatFirstCoordinateRawAmplitude_eq_fourierPowSMulRight
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let ea : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 a)
    let m : Fin 1 → H3FourierPoint3 :=
      fun _ => ea
    VectorFourier.fourierPowSMulRight
        L
        (h3SpectralScalarHeatRawRepresentative ν t G)
        ξ
        1
        m
      =
    h3SpectralScalarHeatFirstCoordinateRawAmplitude
      ν t G a ξ := by
  dsimp only

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  have ha :
      h3FourierDerivativeSymbol a ξ
        =
      ((2 * Real.pi * inner ℝ ξ ea : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [ea]
    rw [h3FourierDerivativeSymbol_eq_inner]
    push_cast
    ring

  simp only [
    VectorFourier.fourierPowSMulRight_apply,
    pow_one,
    Fin.prod_univ_one,
    neg_apply,
    innerSL_apply_apply ℝ,
    smul_eq_mul
  ]

  unfold h3SpectralScalarHeatFirstCoordinateRawAmplitude
  rw [ha]
  dsimp only [ea]
  simp [Complex.real_smul] <;> push_cast <;> ring

/-- One canonical coordinate derivative costs at most the radial first heat
moment. -/
theorem norm_h3SpectralScalarHeatFirstCoordinateRawAmplitude_le_firstMoment
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatFirstCoordinateRawAmplitude
        ν t G a ξ‖
      ≤
    (2 * Real.pi) *
      (‖ξ‖ *
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖) := by
  unfold h3SpectralScalarHeatFirstCoordinateRawAmplitude
  rw [norm_mul]

  have ha :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

  have hHeat :
      0 ≤
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol a ξ‖ *
        ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
        ≤
      h3FourierGradientMagnitude ξ *
        ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ :=
      mul_le_mul_of_nonneg_right ha hHeat
    _ =
      (2 * Real.pi) *
        (‖ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- The first-coordinate raw heat amplitude is integrable at every positive
heat time. -/
theorem h3SpectralScalarHeatFirstCoordinateRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a : Fin 3) :
    Integrable
      (h3SpectralScalarHeatFirstCoordinateRawAmplitude
        ν t G a)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3SpectralScalarHeatFirstCoordinateRawAmplitude
          ν t G a)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SpectralScalarHeatFirstCoordinateRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
        (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
          ν t G)

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ *
            ‖h3SpectralScalarHeatRawRepresentative
              ν t G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    simpa only [pow_one] using
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G 1 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) *
            (‖ξ‖ *
              ‖h3SpectralScalarHeatRawRepresentative
                ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul (2 * Real.pi)

  refine hMajorantInt.mono' hTargetMeas ?_

  exact Filter.Eventually.of_forall fun ξ =>
    norm_h3SpectralScalarHeatFirstCoordinateRawAmplitude_le_firstMoment
      ν t G a ξ

/-- Inverse-Fourier reconstruction of one first-coordinate heat amplitude. -/
noncomputable def h3SpectralScalarHeatFirstCoordinateRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatFirstCoordinateRawAmplitude
      ν t G a)

/-- At positive heat time, the named first-coordinate reconstruction is
exactly the spatial Fréchet derivative of the scalar heat reconstruction
evaluated on the corresponding canonical direction. -/
theorem h3SpectralScalarHeatFirstCoordinateRepresentative_eq_fderiv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatFirstCoordinateRepresentative
        ν t G a x
      =
    (fderiv ℝ
        (h3SpectralScalarHeatC3Representative ν t G)
        x)
      (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let m : Fin 1 → H3FourierPoint3 :=
    fun _ => ea

  have hMom :
      ∀ (n : ℕ), n ≤ (1 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn
    have hn1 : n ≤ 1 := by
      exact_mod_cast hn
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G n (hn1.trans (by norm_num))

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
      (n := 1)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hRawEq :
      (fun ξ : H3FourierPoint3 =>
        VectorFourier.fourierPowSMulRight
          L f ξ 1 m)
        =
      h3SpectralScalarHeatFirstCoordinateRawAmplitude
        ν t G a := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SpectralScalarHeatFirstCoordinateRawAmplitude_eq_fourierPowSMulRight
        ν t G a ξ

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 1)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 1 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

  rw [hRawEq] at hEval
  dsimp only [L] at hEval

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

  rw [hInner] at hEval

  unfold
    h3SpectralScalarHeatFirstCoordinateRepresentative
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SpectralScalarHeatFirstCoordinateRawAmplitude
          ν t G a)
        x
      =
    (fderiv ℝ
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x)
      ea

  simpa only [
    iteratedFDeriv_one_apply,
    m,
    ea
  ] using hEval.symm

end

end Euclidean
end Bridge
end PrimeTensor
