import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Third.Coordinate.Representative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.GeneratorContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive-time continuity of scalar heat third coordinate derivatives

The preceding file identifies each ordered third coordinate derivative of the
positive-time heat reconstruction with inverse Fourier reconstruction of

    D_j(ξ) D_k(ξ) D_l(ξ) heatRaw(ν,t,G,ξ).

At a positive base time `t`, anchor at `a = t / 2`.  For every later time
`s > a`, the raw heat amplitude decreases pointwise in norm, so the entire
third-coordinate integrand is dominated by

    (2π)^3 |ξ|^3 |heatRaw(ν,a,G,ξ)|.

That majorant is integrable by the existing positive-time third-moment theorem.
Pointwise continuity in `s` comes from the already-compiled differentiability
of the raw heat amplitude.  Dominated continuity therefore passes through the
inverse Fourier integral.

The final theorem rewrites the named reconstruction back to the actual
evaluated third Fréchet derivative on the positive-time neighborhood.

No new estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeThirdCoordinateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At every positive heat time and fixed spatial point, each ordered third
coordinate reconstruction is continuous in the heat-time parameter. -/
theorem h3SpectralScalarHeatThirdCoordinateRepresentative_continuousAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3SpectralScalarHeatThirdCoordinateRepresentative
          ν s G j k l x)
      t := by
  let a : ℝ := t / 2
  let S : Set ℝ := Set.Ioi a
  let C : ℝ := (2 * Real.pi) ^ 3

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatThirdCoordinateRawAmplitude
          ν s G j k l ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 3 *
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

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

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
        ((h3SpectralScalarHeatThirdCoordinateRawAmplitude_integrable
          hν (lt_trans ha hs) G j k l).aestronglyMeasurable)

  have h_bound :
      ∀ s ∈ S,
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F s ξ‖ ≤ bound ξ := by
    intro s hs
    filter_upwards with ξ

    have has : a ≤ s := hs.le

    have hThird :=
      norm_h3SpectralScalarHeatThirdCoordinateRawAmplitude_le_thirdMoment
        ν s G j k l ξ

    have hRaw :=
      norm_h3SpectralScalarHeatRawRepresentative_le_of_le_time
        hν has G ξ

    have hMoment :
        ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖
          ≤
        ‖ξ‖ ^ 3 *
            ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖ :=
      mul_le_mul_of_nonneg_left
        hRaw
        (pow_nonneg (norm_nonneg ξ) 3)

    have hScaled :
        C *
            (‖ξ‖ ^ 3 *
              ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖)
          ≤
        C *
            (‖ξ‖ ^ 3 *
              ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖) :=
      mul_le_mul_of_nonneg_left hMoment hC0

    dsimp only [F, bound, C]

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

    rw [norm_mul, hPhaseNorm, one_mul]

    exact hThird.trans hScaled

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3SpectralScalarHeatRawRepresentative_moment_integrable
        hν ha G 3 (by norm_num)

    dsimp only [bound, C]

    exact
      hMoment.const_mul
        ((2 * Real.pi) ^ 3)

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

    have hThirdContinuous :
        Continuous
          (fun s : ℝ =>
            h3SpectralScalarHeatThirdCoordinateRawAmplitude
              ν s G j k l ξ) := by
      unfold h3SpectralScalarHeatThirdCoordinateRawAmplitude
      exact
        continuous_const.mul
          (continuous_const.mul
            (continuous_const.mul
              hRawContinuous))

    dsimp only [F]

    exact
      (continuous_const.mul
        hThirdContinuous).continuousOn

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
        h3SpectralScalarHeatThirdCoordinateRepresentative
          ν s G j k l x) := by
    funext s

    dsimp only [F, phase]

    unfold
      h3SpectralScalarHeatThirdCoordinateRepresentative

    rw [Real.fourierInv_eq']

    simp only [smul_eq_mul]

  rw [← hPathEq]

  exact hIntegralContinuousAt

/-- Every fixed ordered coordinate evaluation of the positive-time heat third
Fréchet derivative is continuous in heat time. -/
theorem h3SpectralScalarHeatC3Representative_thirdFrechet_coordinate_eval_continuousAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (j k l : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        iteratedFDeriv ℝ 3
          (h3SpectralScalarHeatC3Representative ν s G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 j),
            h3FourierAxisDirection (h3AxisOfFin3 k),
            h3FourierAxisDirection (h3AxisOfFin3 l)
          ])
      t := by
  let J : ℝ → ℂ :=
    fun s : ℝ =>
      iteratedFDeriv ℝ 3
        (h3SpectralScalarHeatC3Representative ν s G)
        x
        ![
          h3FourierAxisDirection (h3AxisOfFin3 j),
          h3FourierAxisDirection (h3AxisOfFin3 k),
          h3FourierAxisDirection (h3AxisOfFin3 l)
        ]

  let R : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarHeatThirdCoordinateRepresentative
        ν s G j k l x

  have hR :
      ContinuousAt R t := by
    dsimp only [R]
    exact
      h3SpectralScalarHeatThirdCoordinateRepresentative_continuousAt_time
        hν ht G j k l x

  have hPositive : Set.Ioi (0 : ℝ) ∈ 𝓝 t :=
    Ioi_mem_nhds ht

  have hEq :
      J =ᶠ[𝓝 t] R := by
    filter_upwards [hPositive] with s hs
    dsimp only [J, R]
    symm
    exact
      h3SpectralScalarHeatThirdCoordinateRepresentative_eq_iteratedFDeriv
        hν hs G j k l x

  change ContinuousAt J t
  exact hR.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
