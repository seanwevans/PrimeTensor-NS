import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Second.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Mild.Mass
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Positive-time derivative of the scalar heat second coordinate

`Second.Coordinate.Representative` identifies the ordered mixed Hessian
coordinate of the positive-time heat reconstruction with the inverse Fourier
transform of

    D_a(ξ) D_b(ξ) heatRaw(ν,t,G,ξ).

This file differentiates that representative in heat time.  Its raw derivative
is

    D_a(ξ) D_b(ξ) heatGeneratorRaw(ν,t,G,ξ).

At a positive base time, the two coordinate symbols and the order-two heat
generator cost four Fourier powers.  The already-compiled positive-time
fourth-moment free-heat estimate therefore supplies the local dominated
majorant.

No Navier--Stokes estimate and no time/space commutation is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeSecondCoordinateTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw time-generator amplitude for one ordered mixed heat Hessian
coordinate. -/
noncomputable def h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  h3FourierDerivativeSymbol a ξ *
    (h3FourierDerivativeSymbol b ξ *
      h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G ξ)

/-- The mixed-Hessian heat time-generator raw amplitude is strongly
measurable. -/
theorem h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude_aestronglyMeasurable
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3) :
    AEStronglyMeasurable
      (h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
        ν t G a b)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
  exact
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
        (h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
          ν t G))

/-- Physical inverse-Fourier representative of the mixed-Hessian heat time
generator. -/
noncomputable def h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (a b : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
      ν t G a b)

/-- The positive-time ordered mixed heat Hessian coordinate has an ordinary
time derivative equal to its named second-coordinate heat generator. -/
theorem h3SpectralScalarHeatSecondCoordinateRepresentative_hasDerivAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatSecondCoordinateRepresentative
          ν s G a b x)
      (h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
        ν t G a b x)
      t := by
  let τ : ℝ := t / 2
  let S : Set ℝ := Set.Ioi τ
  let C : ℝ := ν * (2 * Real.pi) ^ 4

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatSecondCoordinateRawAmplitude
          ν s G a b ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
          ν s G a b ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 4 *
          ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖)

  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith

  have hτt : τ < t := by
    dsimp only [τ]
    linarith

  have hS : S ∈ 𝓝 t := by
    dsimp only [S]
    exact Ioi_mem_nhds hτt

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (F s)
          (volume : Measure H3FourierPoint3) := by
    exact Filter.Eventually.of_forall (fun s => by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          ((h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
            ((h3FourierDerivativeSymbol_continuous b).aestronglyMeasurable.mul
              (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
                ν s G))))

  have hF_int :
      Integrable
        (F t)
        (volume : Measure H3FourierPoint3) := by
    have hSecond :=
      h3SpectralScalarHeatSecondCoordinateRawAmplitude_integrable
        hν ht G a b

    have hMeas :
        AEStronglyMeasurable
          (F t)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          hSecond.aestronglyMeasurable

    rw [← integrable_norm_iff hMeas]

    simpa only [
      F,
      phase,
      norm_mul,
      Complex.norm_exp,
      Complex.mul_re,
      Complex.ofReal_re,
      Complex.ofReal_im,
      Complex.I_re,
      Complex.I_im,
      mul_zero,
      zero_mul,
      sub_self,
      Real.exp_zero,
      one_mul
    ] using hSecond.norm

  have hF'_meas :
      AEStronglyMeasurable
        (F' t)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude_aestronglyMeasurable
          ν t G a b)

  have h_bound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, ‖F' s ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro s hs

    have hτs : τ ≤ s := hs.le

    have hDa :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ

    have hDb :=
      norm_h3FourierDerivativeSymbol_le_gradientMagnitude b ξ

    have hDa' :
        ‖h3FourierDerivativeSymbol a ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa only [h3FourierGradientMagnitude] using hDa

    have hDb' :
        ‖h3FourierDerivativeSymbol b ξ‖
          ≤
        (2 * Real.pi) * ‖ξ‖ := by
      simpa only [h3FourierGradientMagnitude] using hDb

    have hGen :=
      norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative_le_anchor
        hν hτs G ξ

    have hInner :
        ‖h3FourierDerivativeSymbol b ξ‖ *
            ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ‖
          ≤
        ((2 * Real.pi) * ‖ξ‖) *
          ((ν * (2 * Real.pi) ^ 2) *
            (‖ξ‖ ^ 2 *
              ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖)) := by
      calc
        ‖h3FourierDerivativeSymbol b ξ‖ *
            ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ‖
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ‖ := by
                exact
                  mul_le_mul_of_nonneg_right
                    hDb'
                    (norm_nonneg _)
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            ((ν * (2 * Real.pi) ^ 2) *
              (‖ξ‖ ^ 2 *
                ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖)) := by
                exact
                  mul_le_mul_of_nonneg_left
                    hGen
                    (by positivity)

    have hAmp :
        ‖h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
            ν s G a b ξ‖
          ≤
        C *
          (‖ξ‖ ^ 4 *
            ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖) := by
      unfold h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude
      rw [norm_mul, norm_mul]

      calc
        ‖h3FourierDerivativeSymbol a ξ‖ *
            (‖h3FourierDerivativeSymbol b ξ‖ *
              ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
                ν s G ξ‖)
            ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (‖h3FourierDerivativeSymbol b ξ‖ *
              ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative
                ν s G ξ‖) := by
                exact
                  mul_le_mul_of_nonneg_right
                    hDa'
                    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤
          ((2 * Real.pi) * ‖ξ‖) *
            (((2 * Real.pi) * ‖ξ‖) *
              ((ν * (2 * Real.pi) ^ 2) *
                (‖ξ‖ ^ 2 *
                  ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖))) := by
                exact
                  mul_le_mul_of_nonneg_left
                    hInner
                    (by positivity)
        _ =
          C *
            (‖ξ‖ ^ 4 *
              ‖h3SpectralScalarHeatRawRepresentative ν τ G ξ‖) := by
                dsimp only [C]
                ring

    dsimp only [F', bound]
    rw [norm_mul]

    have hPhaseNorm : ‖phase ξ‖ = 1 := by
      dsimp only [phase]
      simp only [
        Complex.norm_exp,
        Complex.mul_re,
        Complex.ofReal_re,
        Complex.ofReal_im,
        Complex.I_re,
        Complex.I_im,
        mul_zero,
        zero_mul,
        sub_self,
        Real.exp_zero
      ]

    rw [hPhaseNorm, one_mul]
    exact hAmp

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
        hν hτ G

    dsimp only [bound, C]
    exact
      hMoment.const_mul
        (ν * (2 * Real.pi) ^ 4)

  have h_diff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, HasDerivAt (F · ξ) (F' s ξ) s := by
    filter_upwards with ξ
    intro s hs

    have hRaw :=
      h3SpectralScalarHeatRawRepresentative_hasDerivAt_time
        ν s G ξ

    have hB :=
      HasDerivAt.const_mul
        (h3FourierDerivativeSymbol b ξ)
        hRaw

    have hA :=
      HasDerivAt.const_mul
        (h3FourierDerivativeSymbol a ξ)
        hB

    have hPhase :=
      HasDerivAt.const_mul
        (phase ξ)
        hA

    simpa only [
      F,
      F',
      h3SpectralScalarHeatSecondCoordinateRawAmplitude,
      h3SpectralScalarHeatSecondCoordinateTimeGeneratorRawAmplitude,
      mul_assoc
    ] using hPhase

  have hMain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (F' := F')
      (x₀ := t)
      (s := S)
      (bound := bound)
      (μ := (volume : Measure H3FourierPoint3))
      hS
      hF_meas
      hF_int
      hF'_meas
      h_bound
      bound_integrable
      h_diff

  have hPathEq :
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3, F s ξ)
        =
      (fun s : ℝ =>
        h3SpectralScalarHeatSecondCoordinateRepresentative
          ν s G a b x) := by
    funext s
    dsimp only [F, phase]
    unfold h3SpectralScalarHeatSecondCoordinateRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F' t ξ)
        =
      h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
        ν t G a b x := by
    dsimp only [F', phase]
    unfold h3SpectralScalarHeatSecondCoordinateTimeGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hDeriv := hMain.2
  rw [hPathEq, hGeneratorEq] at hDeriv
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
