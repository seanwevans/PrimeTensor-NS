import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Derivative.FreshRescaledContinuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.C0.Endpoint.FTC
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Rescaled fresh Duhamel tail: fixed-domain integral limit

The previous checkpoint moved the fresh Duhamel tail to the fixed unit interval
and proved the two inputs needed for dominated convergence:

* pointwise convergence for every `u ∈ (0,1)`;
* a lag-uniform selected-path bound on `u ∈ [0,1]`.

This file performs the fixed-domain dominated-convergence step.

For any continuous spectral path with a uniform bound on the rescaled
integrand,

    ∫₀¹ H_{h(1-u)} F(W(t+hu),W(t+hu)) du

tends as `h ↓ 0` to the instantaneous unheated forcing

    F(W(t),W(t)).

The selected restart specialization uses the already-compiled constant
majorant `C_force * (2A) * (2A)`.

This is the quotient limit required for the fresh Duhamel tail.  The next
checkpoint only has to connect this fixed-domain integral to the literal
short interval `∫ₜ^{t+h}` by affine change of variables.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3DuhamelFreshRescaledIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Dominated convergence for the rescaled fresh-tail integral on the fixed
unit interval. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_zero_right_of_bound
    {ν t M : ℝ}
    (hν : 0 < ν)
    (W : ℝ → H3SpectralFinVectorState)
    (hW : Continuous W)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (hBound :
      ∀ h : ℝ, 0 ≤ h →
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          ‖h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
              ν t h W i x u‖ ≤ M) :
    Tendsto
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
            ν t h W i x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) 1)

  let F : ℝ → ℝ → ℂ :=
    fun h u =>
      h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
        ν t h W i x u

  let E : ℂ :=
    h3RawFinLerayOuterProductDivergenceC0Representative
      (W t) (W t) i x

  let bound : ℝ → ℝ :=
    fun _u => M

  have hF_meas :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        AEStronglyMeasurable
          (F h)
          μ := by
    filter_upwards [self_mem_nhdsWithin] with h hh

    by_cases hh0 : h = 0

    · subst h
      have hEq :
          F 0 = fun _u : ℝ => E := by
        funext u
        dsimp only [F, E]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
        simp only [zero_mul, add_zero]
        rw [
          h3RawFinLerayOuterProductDivergenceHeatC3Representative_zero
        ]
      rw [hEq]
      exact continuous_const.aestronglyMeasurable

    · have hhpos : 0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      let R : ℝ → ℂ :=
        fun s =>
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
            ν (t + h) W W i x s

      have hR :
          ContinuousOn
            R
            (Set.Icc t (t + h)) := by
        dsimp only [R]
        exact
          continuousOn_h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath_Icc
            hν
            (by linarith)
            W W hW hW i x

      have hAffine :
          Continuous
            (fun u : ℝ => t + h * u) := by
        fun_prop

      have hMaps :
          MapsTo
            (fun u : ℝ => t + h * u)
            (Set.Icc (0 : ℝ) 1)
            (Set.Icc t (t + h)) := by
        intro u hu
        constructor
        · nlinarith [hu.1, hhpos]
        · nlinarith [hu.2, hhpos]

      have hComp :
          ContinuousOn
            (fun u : ℝ => R (t + h * u))
            (Set.Icc (0 : ℝ) 1) :=
        hR.comp hAffine.continuousOn hMaps

      have hEq :
          F h =
            fun u : ℝ => R (t + h * u) := by
        funext u
        dsimp only [F, R]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
          h3RawFinLerayOuterProductDivergenceHeatC3RetardedPath
        congr 1
        ring

      rw [hEq]

      exact
        (hComp.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable
          measurableSet_Ioo

  have hBoundAE :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ u : ℝ ∂μ,
          ‖F h u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    dsimp only [F, bound]
    exact
      hBound h hh u ⟨hu.1.le, hu.2.le⟩

  have hBoundInt :
      Integrable
        bound
        μ := by
    dsimp only [bound, μ]
    change
      IntegrableOn
        (fun _u : ℝ => M)
        (Set.Ioo (0 : ℝ) 1)
        volume
    rw [
      ← intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ]
    exact intervalIntegrable_const

  have hLim :
      ∀ᵐ u : ℝ ∂μ,
        Tendsto
          (fun h : ℝ => F h u)
          (𝓝[Set.Ici (0 : ℝ)] 0)
          (𝓝 E) := by
    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    dsimp only [F, E]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_zero_right
        hν W hW hu i x

  have hMain :
      Tendsto
        (fun h : ℝ => ∫ u : ℝ, F h u ∂μ)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝 (∫ _u : ℝ, E ∂μ)) := by
    exact
      tendsto_integral_filter_of_dominated_convergence
        (μ := μ)
        (l := (𝓝[Set.Ici (0 : ℝ)] 0))
        (F := F)
        (f := fun _u : ℝ => E)
        (bound := bound)
        hF_meas
        hBoundAE
        hBoundInt
        hLim

  have hPathEq :
      (fun h : ℝ => ∫ u : ℝ, F h u ∂μ)
        =
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
            ν t h W i x u) := by
    funext h
    dsimp only [F, μ]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hLimitEq :
      (∫ _u : ℝ, E ∂μ) = E := by
    dsimp only [μ]
    have hConst :
        (∫ u in (0 : ℝ)..1, E) = E := by
      simp
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hConst
    rw [← restrict_Ioo_eq_restrict_Ioc] at hConst
    exact hConst

  rw [hPathEq, hLimitEq] at hMain
  dsimp only [E] at hMain
  exact hMain

/-- Selected restart specialization of the fixed-domain fresh-tail integral
limit.  Continuity of the selected physical spectral extension is kept as an
explicit hypothesis so this theorem depends only on already-compiled
continuity/boundedness interfaces. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hW :
      Continuous
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀))
    (i : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand
            ν t h W i x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i x)) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  apply
    tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_zero_right_of_bound
      (ν := ν)
      (t := t)
      (M := h3NonlinearForcingL1Coefficient * (2 * A) * (2 * A))
      hν
      W
      hW
      i
      x

  intro h hh u hu

  dsimp only [W]

  exact
    norm_h3RawFinLerayOuterProductDivergenceHeatFreshRescaledIntegrand_selectedRestart_le
      hν U₀ hA hU₀ hh hu i x

end

end Euclidean
end Bridge
end PrimeTensor
