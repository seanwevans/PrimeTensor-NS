import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Forcing.C1.Spatial.Regularity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Endpoint.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Heat.Spatial.Derivative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Classicalization: selected forcing first-derivative heat endpoint

The first-Fréchet fresh-tail rescaling reduces the remaining Duhamel endpoint
problem to the behavior, as the heat lag tends to zero, of one spatial
coordinate derivative of

    H_τ N(W(t), W(t)).

The generic positive-lag derivative theory controls this object using heat
smoothing and therefore carries a `τ⁻¹/²` bound.  At a selected positive
restart time that singular estimate is unnecessary: the unheated forcing
itself already has one raw Fourier moment.

This file uses that selected first moment in two ways.

1. At `τ = 0`, the Fourier multiplier
       d_a(ξ) N̂(W(t),W(t))(ξ)
   is integrable.  Re-running the existing Fourier-kernel spatial
   differentiation argument at zero lag proves that its inverse Fourier
   reconstruction is the genuine coordinate value of the canonical `fderiv`
   of the unheated `C¹` forcing representative.

2. On nonnegative heat lags, the heat multiplier has norm at most one.  The
   same zero-lag derivative amplitude is therefore an integrable dominator,
   and dominated convergence gives
       D_a H_τ N(W(t),W(t)) -> D_a N(W(t),W(t))
   as `τ ↓ 0`.

This is the fixed-state endpoint needed by the fresh first-Fréchet quotient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology Real RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedForcingHeatFirstDerivativeEndpoint
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a selected positive restart time, one coordinate multiplier of the
unheated raw forcing is genuinely Fourier `L¹`. -/
theorem h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierDerivativeSymbol a ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ)
      (volume : Measure H3FourierPoint3) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let F : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  have hZero :
      Integrable F
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hFirst :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_firstMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ * F ξ)
        (volume : Measure H3FourierPoint3) :=
    (h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
      hZero.aestronglyMeasurable

  have hMajorant :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          (2 * Real.pi) * (‖ξ‖ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFirst.const_mul (2 * Real.pi)

  refine hMajorant.mono' hTargetMeas ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul]
    calc
      ‖h3FourierDerivativeSymbol a ξ‖ * ‖F ξ‖
          ≤
        h3FourierGradientMagnitude ξ * ‖F ξ‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h3FourierDerivativeSymbol_le_gradientMagnitude a ξ)
        (norm_nonneg _)
      _ =
        (2 * Real.pi) * (‖ξ‖ * ‖F ξ‖) := by
          unfold h3FourierGradientMagnitude
          ring

/-- At zero heat lag, the coordinate derivative reconstruction is the genuine
derivative of the unheated selected forcing along the corresponding affine
coordinate line. -/
theorem h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_hasDerivAt_coordinate
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
    HasDerivAt
      (fun r : ℝ =>
        h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i
          (x + r • h3FourierAxisDirection (h3AxisOfFin3 a)))
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν 0 (W t) (W t) i a x)
      0 := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
        ν 0 (W t) (W t) i (x + r • e) ξ

  let F' : ℝ → H3FourierPoint3 → ℂ :=
    fun r ξ =>
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
        ν 0 (W t) (W t) i a (x + r • e) ξ

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ‖

  have hRawInt :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W t) (W t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W t) (W t) i

  have hDerivInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ *
            h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ ht htR i a

  have hFInt :
      ∀ r : ℝ,
        Integrable
          (F r)
          (volume : Measure H3FourierPoint3) := by
    intro r
    dsimp only [F]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-(x + r • e))]
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]
    exact hRawInt

  have hFMeas :
      ∀ᶠ r : ℝ in 𝓝 0,
        AEStronglyMeasurable
          (F r)
          (volume : Measure H3FourierPoint3) :=
    Filter.Eventually.of_forall
      (fun r => (hFInt r).aestronglyMeasurable)

  have hF0Int :
      Integrable
        (F 0)
        (volume : Measure H3FourierPoint3) :=
    hFInt 0

  have hF'0Int :
      Integrable
        (F' 0)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [F']
    unfold
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    rw [Real.fourierIntegral_convergent_iff (-(x + (0 : ℝ) • e))]
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]
    simpa using hDerivInt

  have hF'0Meas :
      AEStronglyMeasurable
        (F' 0)
        (volume : Measure H3FourierPoint3) :=
    hF'0Int.aestronglyMeasurable

  have hBoundInt :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound]
    exact hDerivInt.norm

  have hBound :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          ‖F' r ξ‖ ≤ bound ξ := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F', bound]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeFourierKernel
    simp only [Circle.norm_smul]
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]

  have hDiff :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        ∀ r ∈ (Set.univ : Set ℝ),
          HasDerivAt
            (F · ξ)
            (F' r ξ)
            r := by
    filter_upwards with ξ
    intro r hr
    dsimp only [F, F']
    simpa [e] using
      (hasDerivAt_h3RawFinLerayOuterProductDivergenceHeatInverseFourierKernel_coordinate
        ν 0 (W t) (W t) i a x ξ r)

  have hIntegral :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := (Set.univ : Set ℝ))
      (F := F)
      (F' := F')
      (x₀ := (0 : ℝ))
      (bound := bound)
      (μ := (volume : Measure H3FourierPoint3))
      Filter.univ_mem
      hFMeas
      hF0Int
      hF'0Meas
      hBound
      hBoundInt
      hDiff).2

  have hHeatLine :
      HasDerivAt
        (fun r : ℝ =>
          h3RawFinLerayOuterProductDivergenceHeatC3Representative
            ν 0 (W t) (W t) i (x + r • e))
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν 0 (W t) (W t) i a x)
        0 := by
    simpa [
      F,
      F',
      e,
      h3RawFinLerayOuterProductDivergenceHeatC3Representative_eq_integral_kernel,
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_eq_integral_kernel
    ] using hIntegral

  rw [
    h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero
      ν (W t) (W t) i
  ] at hHeatLine

  simpa only [e] using hHeatLine

/-- The zero-lag coordinate derivative reconstruction equals the canonical
Fréchet derivative of the selected unheated forcing evaluated on the same
coordinate direction. -/
theorem h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
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
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν 0 (W t) (W t) i a x
      =
    (fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x)
      (h3FourierAxisDirection (h3AxisOfFin3 a)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let e : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let f : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i

  have hEndpoint :
      HasDerivAt
        (fun r : ℝ => f (x + r • e))
        (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν 0 (W t) (W t) i a x)
        0 := by
    dsimp only [f, e, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_hasDerivAt_coordinate
        hν U₀ hA hU₀ ht htR i a x

  have hC1 :
      ContDiff ℝ 1 f := by
    dsimp only [f, W]
    exact
      h3RawFinLerayOuterProductDivergenceC0Representative_selectedRestart_contDiff_one
        hν U₀ hA hU₀ ht htR i

  have hDiff :
      DifferentiableAt ℝ f x :=
    hC1.differentiable_one.differentiableAt

  have hSmul :
      HasDerivAt
        (fun r : ℝ => r • e)
        e
        0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const e

  have hLine :
      HasDerivAt
        (fun r : ℝ => x + r • e)
        e
        0 :=
    HasDerivAt.const_add x hSmul

  have hDiff0 :
      DifferentiableAt ℝ
        f
        (x + (0 : ℝ) • e) := by
    simpa using hDiff

  have hCanonical0 :=
    hDiff0.hasFDerivAt.comp_hasDerivAt 0 hLine

  change
    HasDerivAt
      (f ∘ fun r : ℝ => x + r • e)
      (h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν 0 (W t) (W t) i a x)
      0
    at hEndpoint

  have hUnique :=
    hEndpoint.unique hCanonical0

  dsimp only [f, e, W] at hUnique
  simpa only [zero_smul, add_zero] using hUnique

/-- At a fixed selected positive time, the positive-lag first-coordinate
derivative reconstruction converges from the right to the canonical spatial
forcing derivative at zero lag. -/
theorem tendsto_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_zero_right
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
    Tendsto
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ (W t) (W t) i a x)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let phase : H3FourierPoint3 → ℂ :=
    fun ξ =>
      Complex.exp
        (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
          Complex.I)

  let F : ℝ → H3FourierPoint3 → ℂ :=
    fun τ ξ =>
      phase ξ *
        (h3FourierDerivativeSymbol a ξ *
          h3RawFinLerayOuterProductDivergenceHeatRepresentative
            ν τ (W t) (W t) i ξ)

  let f0 : H3FourierPoint3 → ℂ :=
    fun ξ =>
      phase ξ *
        (h3FourierDerivativeSymbol a ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ)

  let bound : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ‖h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ‖

  have hPhaseContinuous :
      Continuous phase := by
    dsimp only [phase]
    fun_prop

  have hFMeas :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F τ)
          (volume : Measure H3FourierPoint3) := by
    exact
      Filter.Eventually.of_forall
        (fun τ => by
          dsimp only [F]
          exact
            hPhaseContinuous.aestronglyMeasurable.mul
              ((h3FourierDerivativeSymbol_continuous a).aestronglyMeasurable.mul
                (h3RawFinLerayOuterProductDivergenceHeatRepresentative_aestronglyMeasurable
                  ν τ (W t) (W t) i)))

  have hBoundAE :
      ∀ᶠ τ : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
          ‖F τ ξ‖ ≤ bound ξ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards with ξ

    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ ξ

    have hPhaseNorm :
        ‖phase ξ‖ = 1 := by
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

    dsimp only [F, bound]
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul, hPhaseNorm, one_mul, norm_mul, norm_mul]

    calc
      ‖h3FourierDerivativeSymbol a ξ‖ *
          (‖h3HeatFourierSymbol ν τ ξ‖ *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖)
          ≤
        ‖h3FourierDerivativeSymbol a ξ‖ *
          (1 *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖) := by
            exact
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right
                  hHeat
                  (norm_nonneg _))
                (norm_nonneg _)
      _ =
        ‖h3FourierDerivativeSymbol a ξ *
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖ := by
            rw [one_mul, norm_mul]

  have hBoundInt :
      Integrable
        bound
        (volume : Measure H3FourierPoint3) := by
    dsimp only [bound, W]
    exact
      (h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ ht htR i a).norm

  have hLim :
      ∀ᵐ ξ : H3FourierPoint3 ∂(volume : Measure H3FourierPoint3),
        Tendsto
          (fun τ : ℝ => F τ ξ)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 (f0 ξ)) := by
    filter_upwards with ξ

    have hRaw :=
      tendsto_h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero_right
        (ν := ν) (W t) (W t) i ξ

    dsimp only [F, f0]
    exact
      tendsto_const_nhds.mul
        (tendsto_const_nhds.mul hRaw)

  have hMain :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure H3FourierPoint3))
      (l := (𝓝[Set.Ici (0 : ℝ)] 0))
      (F := F)
      (f := f0)
      bound
      hFMeas
      hBoundAE
      hBoundInt
      hLim

  have hPathEq :
      (fun τ : ℝ =>
        ∫ ξ : H3FourierPoint3, F τ ξ)
        =
      (fun τ : ℝ =>
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν τ (W t) (W t) i a x) := by
    funext τ
    dsimp only [F, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  have hLimitEq :
      (∫ ξ : H3FourierPoint3, f0 ξ)
        =
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν 0 (W t) (W t) i a x := by
    dsimp only [f0, phase]
    unfold
      h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
    rw [
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_zero
        ν (W t) (W t) i
    ]
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]

  rw [hPathEq, hLimitEq] at hMain

  have hEndpoint :=
    h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
      hν U₀ hA hU₀ ht htR i a x

  dsimp only at hEndpoint
  rw [hEndpoint] at hMain

  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
