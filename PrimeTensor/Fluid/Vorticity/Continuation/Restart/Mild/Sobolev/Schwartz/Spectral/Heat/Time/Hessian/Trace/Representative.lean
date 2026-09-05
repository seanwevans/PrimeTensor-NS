import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Time.Laplacian
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Positive-time scalar heat generator as Hessian trace

The nonlinear heat branch already proves the algebraic Fourier-symbol identity

    ∑ j, D_j(ξ) D_j(ξ) = -q(ξ),

where `D_j` is the canonical Fourier derivative symbol and
`q(ξ) = (2π)^2 ‖ξ‖^2`.

This file applies the same identity to the scalar positive-time H³ heat
reconstruction.  Mathlib's explicit second derivative formula for the Fourier
integral identifies the second spatial Frechet derivative on a canonical axis
with inverse Fourier reconstruction of

    D_j(ξ) D_j(ξ) heatRaw(ξ).

Summing the three diagonal directions therefore reconstructs
`-q(ξ) heatRaw(ξ)`.  Multiplication by viscosity is exactly the raw heat time
generator already used in `Heat.Time.Derivative`.

Thus, at every positive heat time,

    heatTimeGenerator
      = ν * ∑ j, D² heat[e_j,e_j].

No new estimate appears here.  Integrability is supplied by the existing
order-two positive-time heat moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeHessianTraceRepresentative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw amplitude corresponding to the diagonal second spatial derivative of
the scalar heat reconstruction in canonical coordinate `j`. -/
noncomputable def h3SpectralScalarHeatSecondDiagonalRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol j ξ *
    (h3FourierDerivativeSymbol j ξ *
      h3SpectralScalarHeatRawRepresentative ν t G ξ)

/-- For inverse Fourier reconstruction, Mathlib's order-two multiplier on one
canonical repeated direction is exactly the project's squared Fourier
derivative symbol. -/
theorem h3SpectralScalarHeatSecondDiagonalRawAmplitude_eq_fourierPowSMulRight
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    let L :
        H3FourierPoint3 →L[ℝ]
          H3FourierPoint3 →L[ℝ] ℝ :=
      -(innerSL ℝ)
    let e : H3FourierPoint3 :=
      h3FourierAxisDirection (h3AxisOfFin3 j)
    let m : Fin 2 → H3FourierPoint3 :=
      fun _ => e
    VectorFourier.fourierPowSMulRight
        L
        (h3SpectralScalarHeatRawRepresentative ν t G)
        ξ
        2
        m
      =
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G j ξ := by
  dsimp only

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 j)

  have hsym :
      h3FourierDerivativeSymbol j ξ
        =
      ((2 * Real.pi * inner ℝ ξ e : ℝ) : ℂ) *
        Complex.I := by
    dsimp only [e]
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

  unfold h3SpectralScalarHeatSecondDiagonalRawAmplitude
  rw [hsym]
  dsimp only [e]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- One repeated coordinate Fourier symbol costs at most the radial second
moment, with the exact Euclidean factor `(2π)^2`. -/
theorem norm_h3SpectralScalarHeatSecondDiagonalRawAmplitude_le_secondMoment
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatSecondDiagonalRawAmplitude
        ν t G j ξ‖
      ≤
    (2 * Real.pi) ^ 2 *
      (‖ξ‖ ^ 2 *
        ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
  unfold h3SpectralScalarHeatSecondDiagonalRawAmplitude
  rw [norm_mul, norm_mul]

  have hj :=
    norm_h3FourierDerivativeSymbol_le_gradientMagnitude j ξ

  have hN :
      0 ≤
        ‖h3SpectralScalarHeatRawRepresentative
          ν t G ξ‖ :=
    norm_nonneg _

  calc
    ‖h3FourierDerivativeSymbol j ξ‖ *
        (‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      h3FourierGradientMagnitude ξ *
        (‖h3FourierDerivativeSymbol j ξ‖ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_right
          hj
          (mul_nonneg (norm_nonneg _) hN)
    _ ≤
      h3FourierGradientMagnitude ξ *
        (h3FourierGradientMagnitude ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hj hN)
          (by
            unfold h3FourierGradientMagnitude
            positivity)
    _ =
      (2 * Real.pi) ^ 2 *
        (‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
      unfold h3FourierGradientMagnitude
      ring

/-- The diagonal second-coordinate raw heat amplitude is integrable at every
positive heat time. -/
theorem h3SpectralScalarHeatSecondDiagonalRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j : Fin 3) :
    Integrable
      (h3SpectralScalarHeatSecondDiagonalRawAmplitude
        ν t G j)
      (volume : Measure H3FourierPoint3) := by
  have hTargetMeas :
      AEStronglyMeasurable
        (h3SpectralScalarHeatSecondDiagonalRawAmplitude
          ν t G j)
        (volume : Measure H3FourierPoint3) := by
    unfold h3SpectralScalarHeatSecondDiagonalRawAmplitude
    exact
      (h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
        ((h3FourierDerivativeSymbol_continuous j).aestronglyMeasurable.mul
          (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
            ν t G))

  have hMomentInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) := by
    exact
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ht G 2 (by norm_num)

  have hMajorantInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMomentInt.const_mul ((2 * Real.pi) ^ 2)

  refine hMajorantInt.mono' hTargetMeas ?_
  filter_upwards with ξ

  exact
    norm_h3SpectralScalarHeatSecondDiagonalRawAmplitude_le_secondMoment
      ν t G j ξ

/-- Physical inverse-Fourier representative of one diagonal second spatial
heat derivative. -/
noncomputable def h3SpectralScalarHeatSecondDiagonalRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (j : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G j)

/-- At positive time, the named diagonal raw reconstruction is exactly the
second Frechet derivative of the scalar heat reconstruction evaluated twice
on the corresponding canonical coordinate direction. -/
theorem h3SpectralScalarHeatSecondDiagonalRepresentative_eq_iteratedFDeriv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j : Fin 3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatSecondDiagonalRepresentative
        ν t G j x
      =
    iteratedFDeriv ℝ 2
      (h3SpectralScalarHeatC3Representative ν t G)
      x
      (fun _ : Fin 2 =>
        h3FourierAxisDirection (h3AxisOfFin3 j)) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let m : Fin 2 → H3FourierPoint3 :=
    fun _ =>
      h3FourierAxisDirection (h3AxisOfFin3 j)

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
      h3SpectralScalarHeatSecondDiagonalRawAmplitude
        ν t G j := by
    funext ξ
    dsimp only [L, f, m]
    exact
      h3SpectralScalarHeatSecondDiagonalRawAmplitude_eq_fourierPowSMulRight
        ν t G j ξ

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

  unfold
    h3SpectralScalarHeatSecondDiagonalRepresentative
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (h3SpectralScalarHeatSecondDiagonalRawAmplitude
          ν t G j)
        x
      =
    iteratedFDeriv ℝ 2
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x m

  exact hEval.symm

/-- Raw trace of the three diagonal second spatial heat amplitudes. -/
noncomputable def h3SpectralScalarHeatLaplacianRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  ∑ j : Fin 3,
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G j ξ

/-- The diagonal raw trace is exactly minus the radial gradient-square
multiplier applied to the positive-time heat amplitude. -/
theorem h3SpectralScalarHeatLaplacianRawAmplitude_eq
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatLaplacianRawAmplitude
        ν t G ξ
      =
    -(h3FourierGradientSquare ξ : ℂ) *
      h3SpectralScalarHeatRawRepresentative ν t G ξ := by
  unfold
    h3SpectralScalarHeatLaplacianRawAmplitude
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [sum_h3FourierDerivativeSymbol_mul_self_eq_neg_gradientSquare]

/-- The raw heat time generator is viscosity times the raw spatial Hessian
trace. -/
theorem h3SpectralScalarHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    h3SpectralScalarHeatTimeGeneratorRawRepresentative
        ν t G ξ
      =
    (ν : ℂ) *
      h3SpectralScalarHeatLaplacianRawAmplitude
        ν t G ξ := by
  unfold h3SpectralScalarHeatTimeGeneratorRawRepresentative
  rw [h3SpectralScalarHeatLaplacianRawAmplitude_eq]
  push_cast
  ring

/-- At positive heat time, the physical raw-trace reconstruction is the sum of
the three diagonal second-Frechet evaluations. -/
theorem h3SpectralScalarHeatLaplacianRepresentative_eq_hessianTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    FourierTransformInv.fourierInv
        (h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
        x
      =
    ∑ j : Fin 3,
      iteratedFDeriv ℝ 2
        (h3SpectralScalarHeatC3Representative ν t G)
        x
        (fun _ : Fin 2 =>
          h3FourierAxisDirection (h3AxisOfFin3 j)) := by
  let A0 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G (0 : Fin 3)

  let A1 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G (1 : Fin 3)

  let A2 : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatSecondDiagonalRawAmplitude
      ν t G (2 : Fin 3)

  have hA0 :
      Integrable A0
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact
      h3SpectralScalarHeatSecondDiagonalRawAmplitude_integrable
        hν ht G (0 : Fin 3)

  have hA1 :
      Integrable A1
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact
      h3SpectralScalarHeatSecondDiagonalRawAmplitude_integrable
        hν ht G (1 : Fin 3)

  have hA2 :
      Integrable A2
        (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact
      h3SpectralScalarHeatSecondDiagonalRawAmplitude_integrable
        hν ht G (2 : Fin 3)

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

  have hInv01 :
      FourierTransformInv.fourierInv (A0 + A1)
        =
      FourierTransformInv.fourierInv A0
        +
      FourierTransformInv.fourierInv A1 := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A0
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A1

    exact
      VectorFourier.fourierIntegral_add
        (e := Real.fourierChar)
        (μ := (volume : Measure H3FourierPoint3))
        (L := -(innerₗ H3FourierPoint3))
        Real.continuous_fourierChar
        hInnerNegContinuous
        hA0
        hA1

  have hInv012 :
      FourierTransformInv.fourierInv ((A0 + A1) + A2)
        =
      FourierTransformInv.fourierInv (A0 + A1)
        +
      FourierTransformInv.fourierInv A2 := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A2

    exact
      VectorFourier.fourierIntegral_add
        (e := Real.fourierChar)
        (μ := (volume : Measure H3FourierPoint3))
        (L := -(innerₗ H3FourierPoint3))
        Real.continuous_fourierChar
        hInnerNegContinuous
        (hA0.add hA1)
        hA2

  have hRaw :
      h3SpectralScalarHeatLaplacianRawAmplitude
          ν t G
        =
      (A0 + A1) + A2 := by
    funext ξ
    unfold h3SpectralScalarHeatLaplacianRawAmplitude
    rw [Fin.sum_univ_three]
    rfl

  rw [hRaw, hInv012, hInv01]
  simp only [Pi.add_apply, Fin.sum_univ_three]

  change
    h3SpectralScalarHeatSecondDiagonalRepresentative
          ν t G (0 : Fin 3) x
      +
      h3SpectralScalarHeatSecondDiagonalRepresentative
          ν t G (1 : Fin 3) x
      +
      h3SpectralScalarHeatSecondDiagonalRepresentative
          ν t G (2 : Fin 3) x
      =
    iteratedFDeriv ℝ 2
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 (0 : Fin 3)))
      +
      iteratedFDeriv ℝ 2
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 (1 : Fin 3)))
      +
      iteratedFDeriv ℝ 2
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 (2 : Fin 3)))

  rw [
    h3SpectralScalarHeatSecondDiagonalRepresentative_eq_iteratedFDeriv
      hν ht G (0 : Fin 3) x,
    h3SpectralScalarHeatSecondDiagonalRepresentative_eq_iteratedFDeriv
      hν ht G (1 : Fin 3) x,
    h3SpectralScalarHeatSecondDiagonalRepresentative_eq_iteratedFDeriv
      hν ht G (2 : Fin 3) x
  ]

/-- Final positive-time heat equation in the exact spatial form needed by the
Duhamel derivative candidate: the heat time generator is viscosity times the
trace of the genuine second spatial Frechet derivative. -/
theorem h3SpectralScalarHeatTimeGeneratorRepresentative_eq_viscosity_mul_hessianTrace
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatTimeGeneratorRepresentative
        ν t G x
      =
    (ν : ℂ) *
      (∑ j : Fin 3,
        iteratedFDeriv ℝ 2
          (h3SpectralScalarHeatC3Representative ν t G)
          x
          (fun _ : Fin 2 =>
            h3FourierAxisDirection (h3AxisOfFin3 j))) := by
  have hRaw :
      h3SpectralScalarHeatTimeGeneratorRawRepresentative
          ν t G
        =
      (ν : ℂ) •
        h3SpectralScalarHeatLaplacianRawAmplitude
          ν t G := by
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul]
    exact
      h3SpectralScalarHeatTimeGeneratorRawRepresentative_eq_viscosity_mul_laplacian
        ν t G ξ

  unfold h3SpectralScalarHeatTimeGeneratorRepresentative

  rw [hRaw]

  have hSmul :
      FourierTransformInv.fourierInv
          ((ν : ℂ) •
            h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
          x
        =
      (ν : ℂ) *
        FourierTransformInv.fourierInv
          (h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
          x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((ν : ℂ) •
            h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
          x
        =
      (ν : ℂ) *
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
          x

    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (h3SpectralScalarHeatLaplacianRawAmplitude ν t G)
          (ν : ℂ))
        x

  rw [hSmul]
  rw [
    h3SpectralScalarHeatLaplacianRepresentative_eq_hessianTrace
      hν ht G x
  ]

end

end Euclidean
end Bridge
end PrimeTensor
