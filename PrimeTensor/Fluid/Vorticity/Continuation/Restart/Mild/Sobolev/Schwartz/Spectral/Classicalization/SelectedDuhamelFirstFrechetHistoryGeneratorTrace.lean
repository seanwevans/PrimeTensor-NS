import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelThirdCoordinateRepresentative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedDuhamelFirstFrechetHistoryRepresentativeQuotient

/-!
# Classicalization: first-Fréchet old-history generator trace

The old-history first-Fréchet quotient now converges to the reconstructed
coordinate heat generator, and the raw generator has already been identified
as

    ν * Σ_k d_a d_k d_k A_t.

`SelectedDuhamelThirdCoordinateRepresentative` identifies each cubic raw
multiplier with the corresponding evaluated genuine third spatial Fréchet
derivative of the literal selected Duhamel integral.

This file passes the raw trace identity through inverse Fourier reconstruction
and closes the old-history contribution in the exact candidate form

    ν * Σ_k D³D(t,x)[e_a,e_k,e_k].

No new estimate, differentiation argument, or mixed-partial interchange is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetHistoryGeneratorTrace
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The reconstructed coordinate old-history generator is viscosity times the
trace of the genuine third spatial Fréchet derivative of the literal selected
Duhamel integral. -/
theorem h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative_eq_viscosity_mul_thirdTrace
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
    h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
        ν A t hν U₀ hA hU₀ ht i a x
      =
    (ν : ℂ) *
      (∑ k : Fin 3,
        iteratedFDeriv ℝ 3
          (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
            ν t W W i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 k)
          ]) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let A0 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelThirdCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a (0 : Fin 3) (0 : Fin 3)

  let A1 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelThirdCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a (1 : Fin 3) (1 : Fin 3)

  let A2 : H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelThirdCoordinateRawAmplitude
      ν A t hν U₀ hA hU₀ ht i a (2 : Fin 3) (2 : Fin 3)

  have hA0 :
      Integrable A0 (volume : Measure H3FourierPoint3) := by
    dsimp only [A0]
    exact
      h3SelectedDuhamelThirdCoordinateRawAmplitude_integrable
        hν U₀ hA hU₀ ht htR i a (0 : Fin 3) (0 : Fin 3)

  have hA1 :
      Integrable A1 (volume : Measure H3FourierPoint3) := by
    dsimp only [A1]
    exact
      h3SelectedDuhamelThirdCoordinateRawAmplitude_integrable
        hν U₀ hA hU₀ ht htR i a (1 : Fin 3) (1 : Fin 3)

  have hA2 :
      Integrable A2 (volume : Measure H3FourierPoint3) := by
    dsimp only [A2]
    exact
      h3SelectedDuhamelThirdCoordinateRawAmplitude_integrable
        hν U₀ hA hU₀ ht htR i a (2 : Fin 3) (2 : Fin 3)

  have hRaw :
      h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude
          ν A t hν U₀ hA hU₀ ht i a
        =
      (ν : ℂ) • ((A0 + A1) + A2) := by
    funext ξ
    rw [
      h3SelectedDuhamelHistoryHeatCoordinateGeneratorRawAmplitude_eq_viscosity_mul_thirdTrace
        hν U₀ hA hU₀ ht i a ξ
    ]
    rw [Fin.sum_univ_three]
    dsimp only [A0, A1, A2, Pi.smul_apply, Pi.add_apply]
    simp only [smul_eq_mul]

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
      FourierTransformInv.fourierInv (A0 + A1) x
        =
      FourierTransformInv.fourierInv A0 x
        +
      FourierTransformInv.fourierInv A1 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A0
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A1
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          hA0
          hA1)
        x

  have hInv012 :
      FourierTransformInv.fourierInv ((A0 + A1) + A2) x
        =
      FourierTransformInv.fourierInv (A0 + A1) x
        +
      FourierTransformInv.fourierInv A2 x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x
        =
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          (A0 + A1)
          x
        +
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          A2
          x

    exact
      congrFun
        (VectorFourier.fourierIntegral_add
          (e := Real.fourierChar)
          (μ := (volume : Measure H3FourierPoint3))
          (L := -(innerₗ H3FourierPoint3))
          Real.continuous_fourierChar
          hInnerNegContinuous
          (hA0.add hA1)
          hA2)
        x

  have hInvSmul :
      FourierTransformInv.fourierInv
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        FourierTransformInv.fourierInv
          ((A0 + A1) + A2)
          x := by
    change
      VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((ν : ℂ) • ((A0 + A1) + A2))
          x
        =
      (ν : ℂ) *
        VectorFourier.fourierIntegral
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          x

    simpa only [Pi.smul_apply, smul_eq_mul] using
      congrFun
        (VectorFourier.fourierIntegral_const_smul
          Real.fourierChar
          (volume : Measure H3FourierPoint3)
          (-(innerₗ H3FourierPoint3))
          ((A0 + A1) + A2)
          (ν : ℂ))
        x

  have hThird0 :=
    h3SelectedDuhamelThirdCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
      hν U₀ hA hU₀ ht htR
      i a (0 : Fin 3) (0 : Fin 3) x

  have hThird1 :=
    h3SelectedDuhamelThirdCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
      hν U₀ hA hU₀ ht htR
      i a (1 : Fin 3) (1 : Fin 3) x

  have hThird2 :=
    h3SelectedDuhamelThirdCoordinateRepresentative_eq_C3Duhamel_iteratedFDeriv
      hν U₀ hA hU₀ ht htR
      i a (2 : Fin 3) (2 : Fin 3) x

  dsimp only [W] at hThird0 hThird1 hThird2

  unfold h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative
  rw [hRaw, hInvSmul, hInv012, hInv01]
  dsimp only [A0, A1, A2]
  rw [hThird0, hThird1, hThird2]
  rw [Fin.sum_univ_three]

/-- Canonical old-history first-Fréchet right-quotient limit: the literal
coordinate Fréchet quotient converges to viscosity times the third spatial
trace appearing in the complete first-Fréchet time-derivative candidate. -/
theorem tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_fderiv_coordinate_zero_right_eq_viscosity_thirdTrace
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
        ((ν : ℂ) *
          (∑ k : Fin 3,
            iteratedFDeriv ℝ 3
              (h3RawFinLerayOuterProductDivergenceHeatC3Duhamel
                ν t W W i)
              x
              ![
                ea,
                h3FourierAxisDirection (h3AxisOfFin3 k),
                h3FourierAxisDirection (h3AxisOfFin3 k)
              ]))) := by
  dsimp only

  have hQ :=
    tendsto_inv_smul_sub_h3SelectedDuhamelHistoryHeat_fderiv_coordinate_zero_right
      hν U₀ hA hU₀ ht htR i a x

  have hGen :=
    h3SelectedDuhamelHistoryHeatCoordinateGeneratorRepresentative_eq_viscosity_mul_thirdTrace
      hν U₀ hA hU₀ ht htR i a x

  dsimp only at hQ hGen ⊢
  rw [hGen] at hQ
  exact hQ

end

end Euclidean
end Bridge
end PrimeTensor
