import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Spectral.Heat.Generator
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Real.C3.Bridge
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Positive-time derivative of the physical H³ heat reconstruction

The low-level spectral heat multiplier now has the exact time generator

    ∂ₜ m(t,ξ) = -ν q(ξ) m(t,ξ).

The existing Schwartz heat-moment layer proves that, at every positive heat
time, the deweighted raw Fourier state has integrable moments through order
three.  This file combines those facts with Mathlib's parametric-integral
differentiation theorem.

For a fixed positive base time `t`, use the neighborhood `(t/2, ∞)`.  Every
later heat multiplier factors through time `t/2`, so the norm of the generator
integrand is bounded by a constant times

    ‖ξ‖² ‖m(t/2,ξ) raw(G)(ξ)‖,

which is integrable by the existing order-two heat-moment theorem.

Consequently the ordinary inverse-Fourier `C³` heat reconstruction is genuinely
differentiable in time at every positive time, with derivative equal to the
inverse Fourier transform of the heat-generator amplitude.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/- Keep real differentiation of complex-valued paths on the same exact
restriction-of-scalars instance used by the spectral generator theorem. -/
attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude of the positive-time heat generator. -/
def h3SpectralScalarHeatTimeGeneratorRawRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) : ℂ :=
  ((-ν * h3FourierGradientSquare ξ : ℝ) : ℂ) *
    h3SpectralScalarHeatRawRepresentative ν t G ξ

/-- The heat-generator raw representative is strongly measurable. -/
theorem h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    AEStronglyMeasurable
      (h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G)
      (volume : Measure H3FourierPoint3) := by
  unfold h3SpectralScalarHeatTimeGeneratorRawRepresentative
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
      (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G)

/-- Exact norm formula for the generator raw representative. -/
theorem norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G ξ‖
      =
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖) := by
  unfold h3SpectralScalarHeatTimeGeneratorRawRepresentative
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

/-- At positive heat time, the generator raw representative is integrable. -/
theorem h3SpectralScalarHeatTimeGeneratorRawRepresentative_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    Integrable
      (h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G)
      (volume : Measure H3FourierPoint3) := by
  have hMoment :=
    h3SpectralScalarHeatRawRepresentative_moment_integrable
      hν ht G 2 (by norm_num)

  rw [← integrable_norm_iff
    (h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
      ν t G)]

  have hScaled :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (ν * (2 * Real.pi) ^ 2) *
            (‖ξ‖ ^ 2 *
              ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  simpa only [
    norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative hν.le G
  ] using hScaled

/-- Heat evolution decreases the pointwise norm of the raw representative as
the positive heat time increases. -/
theorem norm_h3SpectralScalarHeatRawRepresentative_le_of_le_time
    {ν a r : ℝ}
    (hν : 0 < ν)
    (har : a ≤ r)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatRawRepresentative ν r G ξ‖
      ≤
    ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖ := by
  have hb : 0 ≤ r - a := sub_nonneg.mpr har
  have hrsplit : r = a + (r - a) := by ring

  unfold h3SpectralScalarHeatRawRepresentative
  rw [hrsplit, h3HeatFourierSymbol_add]
  repeat' rw [norm_mul]

  have hExtra :
      ‖h3HeatFourierSymbol ν (r - a) ξ‖ ≤ 1 :=
    norm_h3HeatFourierSymbol_le_one hν.le hb ξ

  calc
    ‖h3HeatFourierSymbol ν (r - a) ξ‖ *
          ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3SpectralScalarRawFourier G ξ‖
        ≤
      1 *
          ‖h3HeatFourierSymbol ν a ξ‖ *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
            gcongr
    _ =
      ‖h3HeatFourierSymbol ν a ξ‖ *
        ‖h3SpectralScalarRawFourier G ξ‖ := by ring

/-- On all times after a fixed positive anchor time, the heat-generator
integrand is dominated by the order-two moment at the anchor. -/
theorem norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative_le_anchor
    {ν a r : ℝ}
    (hν : 0 < ν)
    (har : a ≤ r)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    ‖h3SpectralScalarHeatTimeGeneratorRawRepresentative ν r G ξ‖
      ≤
    (ν * (2 * Real.pi) ^ 2) *
      (‖ξ‖ ^ 2 *
        ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖) := by
  rw [
    norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative
      hν.le G ξ
  ]
  have hC : 0 ≤ ν * (2 * Real.pi) ^ 2 := by positivity
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (norm_h3SpectralScalarHeatRawRepresentative_le_of_le_time
          hν har G ξ)
        (sq_nonneg ‖ξ‖))
      hC

/-- Pointwise time derivative of the raw positive-time heat amplitude. -/
theorem h3SpectralScalarHeatRawRepresentative_hasDerivAt_time
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (ξ : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatRawRepresentative ν s G ξ)
      (h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G ξ)
      t := by
  have h :=
    (h3HeatFourierSymbol_hasDerivAt_time ν t ξ).mul_const
      (h3SpectralScalarRawFourier G ξ)

  rw [h3HeatFourierTimeGeneratorSymbol_eq] at h

  simpa only [
    h3SpectralScalarHeatRawRepresentative,
    h3SpectralScalarHeatTimeGeneratorRawRepresentative,
    mul_assoc
  ] using h

/-- Physical inverse-Fourier representative of the heat time generator. -/
noncomputable def h3SpectralScalarHeatTimeGeneratorRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatTimeGeneratorRawRepresentative ν t G)

/-- The positive-time classical heat reconstruction has the expected physical
time derivative at every spatial point. -/
theorem h3SpectralScalarHeatC3Representative_hasDerivAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    HasDerivAt
      (fun s : ℝ =>
        h3SpectralScalarHeatC3Representative ν s G x)
      (h3SpectralScalarHeatTimeGeneratorRepresentative ν t G x)
      t := by
  let a : ℝ := t / 2
  let S : Set ℝ := Set.Ioi a
  let C : ℝ := ν * (2 * Real.pi) ^ 2

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatRawRepresentative ν s G ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatTimeGeneratorRawRepresentative ν s G ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 2 *
          ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖)

  have ha : 0 < a := by
    dsimp only [a]
    linarith

  have hat : a < t := by
    dsimp only [a]
    linarith

  have hS : S ∈ 𝓝 t := by
    dsimp only [S]
    exact Ioi_mem_nhds hat

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
          (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
            ν s G))

  have hF_int :
      Integrable
        (F t)
        (volume : Measure H3FourierPoint3) := by
    have hHeat :=
      h3SpectralScalarHeatRawRepresentative_integrable
        hν ht G
    have hMeas :
        AEStronglyMeasurable
          (F t)
          (volume : Measure H3FourierPoint3) := by
      dsimp only [F]
      exact
        hPhaseContinuous.aestronglyMeasurable.mul
          (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
            ν t G)
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
    ] using hHeat.norm

  have hF'_meas :
      AEStronglyMeasurable
        (F' t)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
          ν t G)

  have h_bound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, ‖F' s ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro s hs
    have has : a ≤ s := hs.le
    have hGen :=
      norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative_le_anchor
        hν has G ξ
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
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ha G 2 (by norm_num)
    dsimp only [bound, C]
    exact hMoment.const_mul (ν * (2 * Real.pi) ^ 2)

  have h_diff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ s ∈ S, HasDerivAt (F · ξ) (F' s ξ) s := by
    filter_upwards with ξ
    intro s hs
    have hRaw :=
      h3SpectralScalarHeatRawRepresentative_hasDerivAt_time
        ν s G ξ
    have hMul :=
      HasDerivAt.const_mul (phase ξ) hRaw
    simpa only [F, F'] using hMul

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
        h3SpectralScalarHeatC3Representative ν s G x) := by
    funext s
    dsimp only [F, phase]
    unfold h3SpectralScalarHeatC3Representative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hGeneratorEq :
      (∫ ξ : H3FourierPoint3, F' t ξ)
        =
      h3SpectralScalarHeatTimeGeneratorRepresentative ν t G x := by
    dsimp only [F', phase]
    unfold h3SpectralScalarHeatTimeGeneratorRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hDeriv := hMain.2
  rw [hPathEq, hGeneratorEq] at hDeriv
  exact hDeriv

end

end Euclidean
end Bridge
end PrimeTensor
