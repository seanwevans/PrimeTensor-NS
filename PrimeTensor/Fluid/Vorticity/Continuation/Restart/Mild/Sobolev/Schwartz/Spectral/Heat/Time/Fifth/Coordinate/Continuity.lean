import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Heat.Time.Fourth.Coordinate.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fifth.Mild.Mass
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive-time continuity of scalar heat fifth coordinate derivatives

The order-three mixed-time closure needs the positive-time fifth spatial heat
trace.  Rather than expanding five coordinate symbols by hand, this file uses
Mathlib's order-generic Fourier multilinear multiplier directly.

For a fixed quintuple of directions `m`, the evaluated multiplier is dominated
by

    C(m) |ξ|⁵ |heatRaw(ν,t,G,ξ)|.

At a positive base time `t`, anchor at `t/2`.  Monotonicity of the heat
amplitude in time and the already-compiled fifth heat moment give an
integrable majorant.  Dominated continuity then yields continuity in the heat
time parameter.

The final theorem specializes to canonical coordinate directions and identifies
the named inverse-Fourier reconstruction with the evaluated fifth Fréchet
derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzHeatTimeFifthCoordinateContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Raw Fourier amplitude for an evaluated fifth spatial Fréchet derivative of
the positive-time scalar heat reconstruction. -/
noncomputable def h3SpectralScalarHeatFifthCoordinateRawAmplitude
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (m : Fin 5 → H3FourierPoint3)
    (ξ : H3FourierPoint3) : ℂ :=
  VectorFourier.fourierPowSMulRight
    (-(innerSL ℝ :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ))
    (h3SpectralScalarHeatRawRepresentative ν t G)
    ξ
    5
    m

/-- Every evaluated fifth-coordinate raw heat amplitude is integrable at
positive heat time. -/
theorem h3SpectralScalarHeatFifthCoordinateRawAmplitude_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (m : Fin 5 → H3FourierPoint3) :
    Integrable
      (h3SpectralScalarHeatFifthCoordinateRawAmplitude
        ν t G m)
      (volume : Measure H3FourierPoint3) := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  have hMeas :
      AEStronglyMeasurable
        f
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G

  have hFive :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 * ‖f ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [f]
    exact
      h3SpectralScalarHeatRawRepresentative_fifthMoment_integrable
        hν ht G

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L hFive hMeas

  have hEvalInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (VectorFourier.fourierPowSMulRight
            L f ξ 5) m)
        (volume : Measure H3FourierPoint3) :=
    ContinuousLinearMap.integrable_comp
      (ContinuousMultilinearMap.apply
        ℝ
        (fun _ : Fin 5 => H3FourierPoint3)
        ℂ
        m)
      hPowInt

  change
    Integrable
      (fun ξ : H3FourierPoint3 =>
        (VectorFourier.fourierPowSMulRight
          (-(innerSL ℝ :
            H3FourierPoint3 →L[ℝ]
              H3FourierPoint3 →L[ℝ] ℝ))
          (h3SpectralScalarHeatRawRepresentative ν t G)
          ξ
          5)
          m)
      (volume : Measure H3FourierPoint3)

  simpa only [L, f] using hEvalInt

/-- Inverse-Fourier reconstruction of an evaluated fifth heat derivative. -/
noncomputable def h3SpectralScalarHeatFifthCoordinateRepresentative
    (ν t : ℝ)
    (G : H3SpectralScalarState)
    (m : Fin 5 → H3FourierPoint3) :
    H3FourierPoint3 → ℂ :=
  FourierTransformInv.fourierInv
    (h3SpectralScalarHeatFifthCoordinateRawAmplitude
      ν t G m)

/-- At positive heat time, the named fifth-coordinate reconstruction is
exactly the fifth Fréchet derivative of the scalar heat reconstruction
evaluated on the same ordered directions. -/
theorem h3SpectralScalarHeatFifthCoordinateRepresentative_eq_iteratedFDeriv
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (m : Fin 5 → H3FourierPoint3)
    (x : H3FourierPoint3) :
    h3SpectralScalarHeatFifthCoordinateRepresentative
        ν t G m x
      =
    iteratedFDeriv ℝ 5
      (h3SpectralScalarHeatC3Representative ν t G)
      x m := by
  let f : H3FourierPoint3 → ℂ :=
    h3SpectralScalarHeatRawRepresentative ν t G

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  have hMom :
      ∀ (n : ℕ), n ≤ (5 : ℕ∞) →
        Integrable
          (fun ξ : H3FourierPoint3 =>
            ‖ξ‖ ^ n * ‖f ξ‖)
          (volume : Measure H3FourierPoint3) := by
    intro n hn

    have hn5 : n ≤ 5 := by
      exact_mod_cast hn

    by_cases hn3 : n ≤ 3
    · dsimp only [f]
      exact
        h3SpectralScalarHeatRawRepresentative_moment_integrable
          hν ht G n hn3
    · have hn4or5 : n = 4 ∨ n = 5 := by
        omega
      rcases hn4or5 with rfl | rfl
      · dsimp only [f]
        exact
          h3SpectralScalarHeatRawRepresentative_fourthMoment_integrable
            hν ht G
      · dsimp only [f]
        exact
          h3SpectralScalarHeatRawRepresentative_fifthMoment_integrable
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
      (n := 5)
      (by norm_num)

  have hEval :=
    congrArg
      (fun F => F x m)
      hDeriv

  have hPowInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            L f ξ 5)
        (volume : Measure H3FourierPoint3) :=
    VectorFourier.integrable_fourierPowSMulRight
      L
      (hMom 5 (by norm_num))
      hMeas

  rw [
    Real.fourierIntegral_continuousMultilinearMap_apply'
      hPowInt
  ] at hEval

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
    h3SpectralScalarHeatFifthCoordinateRepresentative
    h3SpectralScalarHeatFifthCoordinateRawAmplitude
    h3SpectralScalarHeatC3Representative

  change
    VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        (fun ξ : H3FourierPoint3 =>
          VectorFourier.fourierPowSMulRight
            (-(innerSL ℝ :
              H3FourierPoint3 →L[ℝ]
                H3FourierPoint3 →L[ℝ] ℝ))
            f ξ 5 m)
        x
      =
    iteratedFDeriv ℝ 5
      (VectorFourier.fourierIntegral
        Real.fourierChar
        (volume : Measure H3FourierPoint3)
        (-(innerₗ H3FourierPoint3))
        f)
      x m

  simpa only [L] using hEval.symm

/-- At every positive heat time and fixed spatial point, every evaluated fifth
Fréchet reconstruction is continuous in the heat-time parameter. -/
theorem h3SpectralScalarHeatFifthCoordinateRepresentative_continuousAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (m : Fin 5 → H3FourierPoint3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        h3SpectralScalarHeatFifthCoordinateRepresentative
          ν s G m x)
      t := by
  let a : ℝ := t / 2
  let S : Set ℝ := Set.Ioi a

  let L :
      H3FourierPoint3 →L[ℝ]
        H3FourierPoint3 →L[ℝ] ℝ :=
    -(innerSL ℝ)

  let K : ℝ := ∏ k : Fin 5, ‖m k‖

  let C : ℝ :=
    (2 * Real.pi * ‖L‖) ^ 5 * K

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun s ξ =>
      phase ξ *
        h3SpectralScalarHeatFifthCoordinateRawAmplitude
          ν s G m ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      C *
        (‖ξ‖ ^ 5 *
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

  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact Finset.prod_nonneg (fun k _ => norm_nonneg (m k))

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      mul_nonneg
        (pow_nonneg (by positivity) 5)
        hK0

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
        ((h3SpectralScalarHeatFifthCoordinateRawAmplitude_integrable
          hν (lt_trans ha hs) G m).aestronglyMeasurable)

  have h_bound :
      ∀ s ∈ S,
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F s ξ‖ ≤ bound ξ := by
    intro s hs
    filter_upwards with ξ

    have has : a ≤ s := hs.le

    have hRaw :=
      norm_h3SpectralScalarHeatRawRepresentative_le_of_le_time
        hν has G ξ

    have hMoment :
        ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖
          ≤
        ‖ξ‖ ^ 5 *
            ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖ :=
      mul_le_mul_of_nonneg_left
        hRaw
        (pow_nonneg (norm_nonneg ξ) 5)

    have hOp :=
      VectorFourier.norm_fourierPowSMulRight_le
        L
        (h3SpectralScalarHeatRawRepresentative ν s G)
        ξ
        5

    have hEval :
        ‖VectorFourier.fourierPowSMulRight
            L
            (h3SpectralScalarHeatRawRepresentative ν s G)
            ξ
            5
            m‖
          ≤
        ‖VectorFourier.fourierPowSMulRight
            L
            (h3SpectralScalarHeatRawRepresentative ν s G)
            ξ
            5‖ * K := by
      dsimp only [K]
      exact
        (VectorFourier.fourierPowSMulRight
          L
          (h3SpectralScalarHeatRawRepresentative ν s G)
          ξ
          5).le_opNorm m

    have hAmp :
        ‖h3SpectralScalarHeatFifthCoordinateRawAmplitude
            ν s G m ξ‖
          ≤
        C *
          (‖ξ‖ ^ 5 *
            ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖) := by
      unfold h3SpectralScalarHeatFifthCoordinateRawAmplitude
      change
        ‖VectorFourier.fourierPowSMulRight
            L
            (h3SpectralScalarHeatRawRepresentative ν s G)
            ξ
            5
            m‖
          ≤
        C *
          (‖ξ‖ ^ 5 *
            ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖)
      calc
        ‖VectorFourier.fourierPowSMulRight
            L
            (h3SpectralScalarHeatRawRepresentative ν s G)
            ξ
            5
            m‖
            ≤
          ‖VectorFourier.fourierPowSMulRight
              L
              (h3SpectralScalarHeatRawRepresentative ν s G)
              ξ
              5‖ * K := hEval
        _ ≤
          ((2 * Real.pi * ‖L‖) ^ 5 *
              ‖ξ‖ ^ 5 *
              ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖) * K := by
          exact mul_le_mul_of_nonneg_right hOp hK0
        _ =
          C *
            (‖ξ‖ ^ 5 *
              ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖) := by
          dsimp only [C]
          ring

    have hScaled :
        C *
            (‖ξ‖ ^ 5 *
              ‖h3SpectralScalarHeatRawRepresentative ν s G ξ‖)
          ≤
        C *
            (‖ξ‖ ^ 5 *
              ‖h3SpectralScalarHeatRawRepresentative ν a G ξ‖) :=
      mul_le_mul_of_nonneg_left hMoment hC0

    dsimp only [F, bound]

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

    exact hAmp.trans hScaled

  have bound_integrable :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    have hMoment :=
      h3SpectralScalarHeatRawRepresentative_fifthMoment_integrable
        hν ha G

    dsimp only [bound]

    exact hMoment.const_mul C

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

    have hAmpContinuous :
        Continuous
          (fun s : ℝ =>
            h3SpectralScalarHeatFifthCoordinateRawAmplitude
              ν s G m ξ) := by
      unfold h3SpectralScalarHeatFifthCoordinateRawAmplitude
      change
        Continuous
          (fun s : ℝ =>
            VectorFourier.fourierPowSMulRight
              L
              (h3SpectralScalarHeatRawRepresentative ν s G)
              ξ
              5
              m)
      simp_rw [VectorFourier.fourierPowSMulRight_eq_comp]
      fun_prop

    dsimp only [F]

    exact
      (continuous_const.mul
        hAmpContinuous).continuousOn

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
        h3SpectralScalarHeatFifthCoordinateRepresentative
          ν s G m x) := by
    funext s

    dsimp only [F, phase]

    unfold
      h3SpectralScalarHeatFifthCoordinateRepresentative

    rw [Real.fourierInv_eq']

    simp only [smul_eq_mul]

  rw [← hPathEq]

  exact hIntegralContinuousAt

/-- Every fixed ordered canonical-coordinate evaluation of the positive-time
heat fifth Fréchet derivative is continuous in heat time. -/
theorem h3SpectralScalarHeatC3Representative_fifthFrechet_coordinate_eval_continuousAt_time
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState)
    (a b c d e : Fin 3)
    (x : H3FourierPoint3) :
    ContinuousAt
      (fun s : ℝ =>
        iteratedFDeriv ℝ 5
          (h3SpectralScalarHeatC3Representative ν s G)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b),
            h3FourierAxisDirection (h3AxisOfFin3 c),
            h3FourierAxisDirection (h3AxisOfFin3 d),
            h3FourierAxisDirection (h3AxisOfFin3 e)
          ])
      t := by
  let m : Fin 5 → H3FourierPoint3 :=
    ![
      h3FourierAxisDirection (h3AxisOfFin3 a),
      h3FourierAxisDirection (h3AxisOfFin3 b),
      h3FourierAxisDirection (h3AxisOfFin3 c),
      h3FourierAxisDirection (h3AxisOfFin3 d),
      h3FourierAxisDirection (h3AxisOfFin3 e)
    ]

  let J : ℝ → ℂ :=
    fun s : ℝ =>
      iteratedFDeriv ℝ 5
        (h3SpectralScalarHeatC3Representative ν s G)
        x m

  let R : ℝ → ℂ :=
    fun s : ℝ =>
      h3SpectralScalarHeatFifthCoordinateRepresentative
        ν s G m x

  have hR :
      ContinuousAt R t := by
    dsimp only [R]
    exact
      h3SpectralScalarHeatFifthCoordinateRepresentative_continuousAt_time
        hν ht G m x

  have hPositive : Set.Ioi (0 : ℝ) ∈ 𝓝 t :=
    Ioi_mem_nhds ht

  have hEq :
      J =ᶠ[𝓝 t] R := by
    filter_upwards [hPositive] with s hs
    dsimp only [J, R]
    symm
    exact
      h3SpectralScalarHeatFifthCoordinateRepresentative_eq_iteratedFDeriv
        hν hs G m x

  change ContinuousAt J t
  exact hR.congr_of_eventuallyEq hEq

end

end Euclidean
end Bridge
end PrimeTensor
