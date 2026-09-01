import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Derivative
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive-time continuity of the physical heat time generator

`Heat.Time.Derivative` identifies the positive-time derivative of the classical
heat reconstruction with the inverse Fourier reconstruction of

    (-ν q(ξ)) m(ν,t,ξ) raw(G)(ξ).

For the temporal regularity closure we also need the generator value itself to
depend continuously on the positive heat time.

No new estimate is required.  At a positive base time `t`, work on
`(t / 2, ∞)`.  The existing anchor estimate dominates every generator
integrand on this neighborhood by the order-two heat moment at `t / 2`, which
is integrable.  Pointwise continuity in the time parameter follows from the
already-proved pointwise time differentiability of the raw heat amplitude.
Mathlib's dominated continuity theorem then moves continuity through the
inverse-Fourier integral.

This is deliberately a scalar, fixed-spatial-point theorem.  It is exactly the
form needed for the Hessian-trace rewrite of the Duhamel temporal derivative
candidate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeGeneratorContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every positive heat time and fixed spatial point, the physical heat
time-generator representative is continuous in the heat-time parameter. -/
theorem h3SpectralScalarHeatTimeGeneratorRepresentative_continuousAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3SpectralScalarHeatTimeGeneratorRepresentative
          ν s G x)
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
        h3SpectralScalarHeatTimeGeneratorRawRepresentative
          ν s G ξ

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

  have htS : t ∈ S := by
    exact hat

  have hSnhds : S ∈ 𝓝 t := by
    dsimp only [S]
    exact Ioi_mem_nhds hat

  have hPhaseContinuous : Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hF_meas :
      ∀ s ∈ S,
        AEStronglyMeasurable
          (F s)
          (volume : Measure H3FourierPoint3) := by
    intro s hs
    dsimp only [F]
    exact
      hPhaseContinuous.aestronglyMeasurable.mul
        (h3SpectralScalarHeatTimeGeneratorRawRepresentative_aestronglyMeasurable
          ν s G)

  have h_bound :
      ∀ s ∈ S,
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F s ξ‖ ≤ bound ξ := by
    intro s hs
    filter_upwards with ξ

    have has : a ≤ s := hs.le

    have hGen :=
      norm_h3SpectralScalarHeatTimeGeneratorRawRepresentative_le_anchor
        hν has G ξ

    dsimp only [F, bound, C]

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

    exact
      hMoment.const_mul
        (ν * (2 * Real.pi) ^ 2)

  have h_cont :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ContinuousOn
          (fun s : ℝ => F s ξ)
          S := by
    filter_upwards with ξ

    have hRawContinuous :
        Continuous
          (fun s : ℝ =>
            h3SpectralScalarHeatRawRepresentative
              ν s G ξ) := by
      rw [continuous_iff_continuousAt]
      intro s
      exact
        (h3SpectralScalarHeatRawRepresentative_hasDerivAt_time
          ν s G ξ).continuousAt

    have hGeneratorContinuous :
        Continuous
          (fun s : ℝ =>
            h3SpectralScalarHeatTimeGeneratorRawRepresentative
              ν s G ξ) := by
      unfold
        h3SpectralScalarHeatTimeGeneratorRawRepresentative
      exact
        continuous_const.mul
          hRawContinuous

    dsimp only [F]

    exact
      (continuous_const.mul
        hGeneratorContinuous).continuousOn

  have hIntegralContinuousOn :
      ContinuousOn
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, F s ξ)
        S := by
    exact
      continuousOn_of_dominated
        hF_meas
        h_bound
        bound_integrable
        h_cont

  have hIntegralContinuousAt :
      ContinuousAt
        (fun s : ℝ =>
          ∫ ξ : H3FourierPoint3, F s ξ)
        t := by
    exact
      (hIntegralContinuousOn t htS).continuousAt
        hSnhds

  have hPathEq :
      (fun s : ℝ =>
        ∫ ξ : H3FourierPoint3, F s ξ)
        =
      (fun s : ℝ =>
        h3SpectralScalarHeatTimeGeneratorRepresentative
          ν s G x) := by
    funext s

    dsimp only [F, phase]

    unfold
      h3SpectralScalarHeatTimeGeneratorRepresentative

    rw [Real.fourierInv_eq']

    simp only [smul_eq_mul]

  rw [← hPathEq]

  exact hIntegralContinuousAt

end

end Euclidean
end Bridge
end PrimeTensor
