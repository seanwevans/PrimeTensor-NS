import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.C3.Bridge

/-!
# Positive-lag time derivative of the nonlinear heat reconstruction

The fixed nonlinear forcing state is not itself used here as a weighted H³
state.  Instead we differentiate its already-established raw positive-lag
Fourier representation directly.

The proof is the exact nonlinear analogue of `Heat.Time.Derivative`.

* the heat-symbol derivative contributes
  `-ν * h3FourierGradientSquare ξ`;
* the order-two Fourier moment supplied by the nonlinear `C³` bridge makes
  the generator amplitude integrable;
* on the neighborhood `(τ/2, ∞)`, heat monotonicity dominates every nearby
  generator integrand by the order-two moment at the fixed anchor `τ/2`;
* Mathlib's dominated parametric-integral theorem then differentiates the
  inverse Fourier integral.

Thus the ordinary fixed-lag nonlinear heat reconstruction has a genuine time
derivative at every positive lag.  This is the terminal-heat-parameter piece
needed for the diagonal Duhamel derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3NonlinearHeatTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/- Keep real differentiation of complex-valued paths on the same exact
restriction-of-scalars instance used by the free heat derivative theorem. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude of the time generator applied to one fixed nonlinear
forcing coordinate. -/
def h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ) *
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ U V i ξ

/-- The nonlinear heat-generator raw amplitude is strongly measurable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    AEStronglyMeasurable
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν τ U V i)
      (volume : Measure H3FourierPoint3) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
  have hCoeff :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ))
        (volume : Measure H3FourierPoint3) := by
    apply Continuous.aestronglyMeasurable
    unfold h3FourierGradientSquare
    fun_prop
  exact
    hCoeff.mul
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
        ν τ U V i)

/-- Exact norm formula for the nonlinear heat-generator raw amplitude. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
    {ν τ : ℝ}
    (hν : 0 ≤ ν)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν τ U V i ξ‖
      =
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i ξ‖) := by
  unfold h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hq : 0 ≤ h3FourierGradientSquare ξ :=
    h3FourierGradientSquare_nonneg ξ
  have hνq : 0 ≤ ν * h3FourierGradientSquare ξ :=
    mul_nonneg hν hq
  rw [show -ν * h3FourierGradientSquare ξ =
      -(ν * h3FourierGradientSquare ξ) by ring]
  rw [abs_neg, abs_of_nonneg hνq]
  unfold h3FourierGradientSquare
  ring

/-- At every positive heat lag, the nonlinear time-generator raw amplitude is
integrable. -/
theorem h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_integrable
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    Integrable
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν τ U V i)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
      hν hτ U V i 2 (by norm_num)

  rw [← integrable_norm_iff
    (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
      ν τ U V i)]

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 2) *
            (‖ξ‖ ^ 2 *
              ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
                ν τ U V i ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  simpa only [
    norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
      hν.le U V i
  ] using hScaled

/-- Increasing the positive heat lag can only decrease the pointwise norm of
the nonlinear raw heat representative. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatRepresentative_le_of_le_time
    {ν a r : ℝ}
    (hν : 0 < ν)
    (har : a ≤ r)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν r U V i ξ‖
      ≤
    ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
        ν a U V i ξ‖ := by
  have hb : 0 ≤ r - a := sub_nonneg.mpr har
  have hrsplit : r = a + (r - a) := by ring

  unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
  rw [hrsplit, h3HeatFourierSymbol_add]
  repeat' rw [norm_mul]

  have hExtra :
      ‖h3HeatFourierSymbol ν (r - a) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hb ξ

  calc
    ‖h3HeatFourierSymbol ν (r - a) ξ‖ *
          ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖
        ≤
      1 *
          ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by
            gcongr
    _ =
      ‖h3HeatFourierSymbol ν a ξ‖ *
        ‖h3RawFinLerayOuterProductDivergence U V i ξ‖ := by ring

/-- On all lags after a fixed positive anchor, the nonlinear generator
integrand is dominated by the order-two moment at the anchor. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_le_anchor
    {ν a r : ℝ}
    (hν : 0 < ν)
    (har : a ≤ r)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    ‖h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν r U V i ξ‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν a U V i ξ‖) := by
  rw [
    norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
      hν.le U V i ξ
  ]
  have hC : 0 ≤ ν * (2 * Real.pi) ^ 2 := by positivity
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (norm_h3RawFinLerayOuterProductDivergenceHeatRepresentative_le_of_le_time
          hν har U V i ξ)
        (sq_nonneg ‖ξ‖))
      hC

/-- Pointwise time derivative of the fixed nonlinear raw heat amplitude. -/
theorem h3RawFinLerayOuterProductDivergenceHeatRepresentative_hasDerivAt_time
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν r U V i ξ)
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
        ν τ U V i ξ)
      τ := by
  have h :=
    (h3HeatFourierSymbol_hasDerivAt_time ν τ ξ).mul_const
      (h3RawFinLerayOuterProductDivergence U V i ξ)

  rw [h3HeatFourierTimeGeneratorSymbol_eq] at h

  simpa only [
    h3RawFinLerayOuterProductDivergenceHeatRepresentative,
    h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative,
    mul_assoc
  ] using h

/-- Physical inverse-Fourier representative of the nonlinear heat time
generator. -/
noncomputable def h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
    (ν τ : ℝ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
      ν τ U V i)

/-- The positive-lag classical nonlinear heat reconstruction has the expected
ordinary time derivative at every spatial point. -/
theorem h3RawFinLerayOuterProductDivergenceHeatC3Representative_hasDerivAt_time
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (U V : H3SpectralFinVectorState)
    (i : Fin 3)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν r U V i x)
      (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν τ U V i x)
      τ := by
  let a : ℝ := τ / 2
  let S : Set ℝ := Set.Ioi a
  let C : ℝ := ν * (2 * Real.pi) ^ 2

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      phase ξ *
        h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν r U V i ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      phase ξ *
        h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative
          ν r U V i ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν a U V i ξ‖)

  have ha : 0 < a := by
    dsimp only [a]
    linarith

  have hat : a < τ := by
    dsimp only [a]
    linarith

  have hS : S ∈ 𝓝 τ := by
    dsimp only [S]
    exact Ioi_mem_nhds hat

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hF_meas :
      ∀ᶠ r in 𝓝 τ,
        AEStronglyMeasurable
          (F r)
          (volume : Measure H3FourierPoint3) := by
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
            ν r U V i))

  have hHeatInt :
      Integrable
        (h3RawFinLerayOuterProductDivergenceHeatRepresentative
          ν τ U V i)
        (volume : Measure H3FourierPoint3) := by
    rw [← integrable_norm_iff
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
        ν τ U V i)]
    simpa using
      (h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ U V i 0 (by norm_num))

  have hF_int :
      Integrable
        (F τ)
        (volume : Measure H3FourierPoint3) := by
    have hMeas :
        AEStronglyMeasurable
          (F τ)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
            ν τ U V i)
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
    ] using hHeatInt.norm

  have hF'_meas :
      AEStronglyMeasurable
        (F' τ)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
          ν τ U V i)

  have h_bound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ S, ‖F' r ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro r hr
    have har : a ≤ r := hr.le
    have hGen :=
      norm_h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRawRepresentative_le_anchor
        hν har U V i ξ
    dsimp only [F', bound, C]
    simpa only [
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
    ] using hGen

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν ha U V i 2 (by norm_num)
    dsimp only [bound, C]
    exact hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  have h_diff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ S, HasDerivAt (F · ξ) (F' r ξ) r := by
    filter_upwards with ξ
    intro r hr
    have hRaw :=
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_hasDerivAt_time
        ν r U V i ξ
    have hMul :=
      HasDerivAt.const_mul (phase ξ) hRaw
    simpa only [F, F'] using hMul

  have hMain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F)
      (F' := F')
      (x₀ := τ)
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
      (fun r : ℝ =>
        ∫ ξ : H3FourierPoint3, F r ξ)
        =
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatC3Representative
          ν r U V i x) := by
    funext r
    dsimp only [F, phase]
    unfold h3RawFinLerayOuterProductDivergenceHeatC3Representative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F' τ ξ)
        =
      h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
        ν τ U V i x := by
    dsimp only [F', phase]
    unfold h3RawFinLerayOuterProductDivergenceHeatTimeGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hDeriv := hMain.2
  rw [hPathEq, hGeneratorEq] at hDeriv
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
