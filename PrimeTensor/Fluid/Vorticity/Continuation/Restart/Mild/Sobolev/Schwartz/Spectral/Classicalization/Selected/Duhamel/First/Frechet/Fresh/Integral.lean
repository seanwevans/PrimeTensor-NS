import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.First.Frechet.Fresh.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Path.Derivative.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Classicalization: first-Fréchet fresh-tail fixed-domain integral

The rescaled first-Fréchet fresh integrand now converges pointwise on
`u ∈ (0,1)` to the instantaneous selected forcing derivative.

This file supplies the remaining fixed-domain dominated-convergence step.

The useful domination is local in `h`, not global in time.  Put

    M(r) = ∫ |ξ| |N̂(W(r),W(r)) - N̂(W(t),W(t))|.

The selected forcing first-mass continuity theorem gives `M(r) → 0` as
`r → t`.  Hence there is a neighborhood of `t` on which `M(r) < 1`.
For sufficiently small nonnegative `h`, every `t + h u`, `u ∈ [0,1]`,
lies in that neighborhood and remains inside the restart interval.

For positive heat lag, contractivity gives a uniform bound on the fixed
`W(t)` coordinate derivative by the zero-lag derivative Fourier mass.  The
moving-state difference estimate from the preceding checkpoint then yields a
single constant dominator on the unit interval.

Dominated convergence therefore proves that the rescaled first-Fréchet fresh
integral converges to the instantaneous forcing coordinate derivative.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelFirstFrechetFreshIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a selected positive time, positive heat lag cannot increase the
pointwise inverse-Fourier coordinate derivative beyond the unheated coordinate
derivative Fourier `L¹` mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_le_unheatedDerivativeMass
    {ν A t τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hτ : 0 < τ)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
        ν τ (W t) (W t) i a x‖
      ≤
    ∫ ξ : H3FourierPoint3,
      ‖h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ‖ := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let raw : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let heated : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergenceHeatRepresentative
      ν τ (W t) (W t) i

  have hHeatDerivInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ * heated ξ)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [heated]
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_derivative_integrable
        hν hτ (W t) (W t) i a

  have hRawDerivInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierDerivativeSymbol a ξ * raw ξ)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_derivative_integrable
        hν U₀ hA hU₀ ht htR i a

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol a ξ * heated ξ‖
          ≤
        ‖h3FourierDerivativeSymbol a ξ * raw ξ‖ := by
    intro ξ
    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ
    dsimp only [heated, raw]
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    simp only [norm_mul]
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
        ‖h3FourierDerivativeSymbol a ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖ := by
          rw [one_mul]

  have hIntegral :
      (∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol a ξ * heated ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖h3FourierDerivativeSymbol a ξ * raw ξ‖ := by
    exact
      integral_mono_ae
        hHeatDerivInt.norm
        hRawDerivInt.norm
        (Filter.Eventually.of_forall hPoint)

  exact
    (norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_le_integral
      hν hτ (W t) (W t) i a x).trans hIntegral

/-- The selected rescaled first-Fréchet fresh integral converges from the right
to the instantaneous forcing derivative in the chosen coordinate direction. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
            ν t h W i a x u)
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

  let ea : H3FourierPoint3 :=
    h3FourierAxisDirection (h3AxisOfFin3 a)

  let E : ℂ :=
    (fderiv ℝ
        (h3RawFinLerayOuterProductDivergenceC0Representative
          (W t) (W t) i)
        x) ea

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖

  let J : ℝ :=
    ∫ ξ : H3FourierPoint3,
      ‖h3FourierDerivativeSymbol a ξ *
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ‖

  let B : ℝ :=
    h3FourierFirstDerivativeL1Coefficient * ‖ea‖ + J + ‖E‖

  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) 1)

  let F : ℝ → ℝ → ℂ :=
    fun h u =>
      h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
        ν t h W i a x u

  let bound : ℝ → ℝ :=
    fun _u => B

  have hWcont :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hMassBase :
      Tendsto
        M
        (𝓝 t)
        (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceFirstMass_tendsto_zero
        hν U₀ hA hU₀ ht htR i

  have hMassNhds :
      M ⁻¹' Set.Iio (1 : ℝ) ∈ 𝓝 t := by
    exact
      hMassBase
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

  rcases Metric.mem_nhds_iff.1 hMassNhds with
    ⟨ε, hε, hεball⟩

  let R : ℝ :=
    h3FinHeatLerayRestartRadius ν A

  let δ : ℝ :=
    min ε (R - t)

  have hRt :
      0 < R - t := by
    dsimp only [R]
    linarith

  have hδ :
      0 < δ := by
    dsimp only [δ]
    exact lt_min hε hRt

  have hSmall :
      Set.Iio δ ∈ (𝓝[Set.Ici (0 : ℝ)] 0) := by
    exact
      mem_inf_of_left
        (Iio_mem_nhds hδ)

  have hJnonneg :
      0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg (fun ξ => norm_nonneg _)

  have hCoeffNonneg :
      0 ≤ h3FourierFirstDerivativeL1Coefficient :=
    h3FourierFirstDerivativeL1Coefficient_nonneg

  have hBnonneg :
      0 ≤ B := by
    dsimp only [B]
    positivity

  have hFMeas :
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
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        simp only [zero_mul, add_zero, sub_self]
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
            hν U₀ hA hU₀ ht htR.le i a x
        ]
      rw [hEq]
      exact continuous_const.aestronglyMeasurable

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      let P : ℝ → ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
          ν (t + h) W W i a x

      have hP :
          ContinuousOn
            P
            (Set.Ioo (0 : ℝ) (t + h)) := by
        dsimp only [P]
        exact
          continuousOn_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath_Ioo
            hν W W hWcont hWcont i a x

      have hAffine :
          Continuous
            (fun u : ℝ => t + h * u) := by
        fun_prop

      have hMaps :
          MapsTo
            (fun u : ℝ => t + h * u)
            (Set.Ioo (0 : ℝ) 1)
            (Set.Ioo (0 : ℝ) (t + h)) := by
        intro u hu
        constructor
        · have hhu :
              0 ≤ h * u := by
            exact mul_nonneg hh hu.1.le
          linarith
        · have huu :
              h * u < h := by
            have hlt : u < 1 := hu.2
            nlinarith
          linarith

      have hComp :
          ContinuousOn
            (fun u : ℝ => P (t + h * u))
            (Set.Ioo (0 : ℝ) 1) :=
        hP.comp hAffine.continuousOn hMaps

      have hEq :
          F h =
            fun u : ℝ => P (t + h * u) := by
        funext u
        dsimp only [F, P]
        exact
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
            ν t h W i a x u

      rw [hEq]

      exact
        hComp.aestronglyMeasurable
          measurableSet_Ioo

  have hBoundAE :
      ∀ᶠ h : ℝ in (𝓝[Set.Ici (0 : ℝ)] 0),
        ∀ᵐ u : ℝ ∂μ,
          ‖F h u‖ ≤ bound u := by
    filter_upwards
      [self_mem_nhdsWithin, hSmall]
      with h hh hhd

    dsimp only [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu

    have huu :
        h * u ≤ h := by
      have hu1 : u ≤ 1 := hu.2.le
      calc
        h * u ≤ h * 1 :=
          mul_le_mul_of_nonneg_left hu1 hh
        _ = h := by ring

    have hhu0 :
        0 ≤ h * u :=
      mul_nonneg hh hu.1.le

    have hδeps :
        δ ≤ ε := by
      dsimp only [δ]
      exact min_le_left _ _

    have hδR :
        δ ≤ R - t := by
      dsimp only [δ]
      exact min_le_right _ _

    have hhuε :
        h * u < ε := by
      calc
        h * u ≤ h := huu
        _ < δ := hhd
        _ ≤ ε := hδeps

    have hdist :
        dist (t + h * u) t < ε := by
      rw [Real.dist_eq]
      have hsub :
          t + h * u - t = h * u := by
        ring
      rw [hsub, abs_of_nonneg hhu0]
      exact hhuε

    have hMlt :
        M (t + h * u) < 1 :=
      hεball hdist

    have hri :
        t + h * u ∈ Set.Ioo (0 : ℝ) R := by
      constructor
      · linarith
      · have hhuR :
            h * u < R - t := by
          calc
            h * u ≤ h := huu
            _ < δ := hhd
            _ ≤ R - t := hδR
        linarith

    by_cases hh0 : h = 0

    · subst h
      dsimp only [F, bound, B]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
      ]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
      simp only [zero_mul, add_zero, sub_self]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_zero_eq_selectedRestart_fderiv_apply
          hν U₀ hA hU₀ ht htR.le i a x
      ]
      dsimp only [E, ea]
      have hLeft :
          0 ≤
            h3FourierFirstDerivativeL1Coefficient *
              ‖h3FourierAxisDirection (h3AxisOfFin3 a)‖ + J := by
        positivity
      linarith [norm_nonneg
        ((fderiv ℝ
            (h3RawFinLerayOuterProductDivergenceC0Representative
              (W t) (W t) i)
            x)
          (h3FourierAxisDirection (h3AxisOfFin3 a)))]

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      have hu1 :
          0 < 1 - u := by
        linarith [hu.2]

      have hlag :
          0 < h * (1 - u) :=
        mul_pos hhpos hu1

      have hLagEq :
          (t + h) - (t + h * u)
            =
          h * (1 - u) := by
        ring

      let Q : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a x

      let T : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative
          ν (h * (1 - u))
          (W t) (W t)
          i a x

      have hFEq :
          F h u = Q := by
        dsimp only [F, Q]
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_eq_firstDerivativeRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRetardedPath
        rw [hLagEq]

      have hMove :
          ‖Q - T‖
            ≤
          (h3FourierFirstDerivativeL1Coefficient *
            M (t + h * u)) * ‖ea‖ := by
        dsimp only [Q, T, M, ea, W, R] at hri ⊢
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_sub_le_differenceFirstMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a x

      have hMoveOne :
          ‖Q - T‖
            ≤
          h3FourierFirstDerivativeL1Coefficient * ‖ea‖ := by
        calc
          ‖Q - T‖
              ≤
            (h3FourierFirstDerivativeL1Coefficient *
              M (t + h * u)) * ‖ea‖ :=
            hMove
          _ ≤
            (h3FourierFirstDerivativeL1Coefficient * 1) * ‖ea‖ := by
              gcongr
          _ =
            h3FourierFirstDerivativeL1Coefficient * ‖ea‖ := by
              ring

      have hFixed :
          ‖T‖ ≤ J := by
        dsimp only [T, J, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatFirstDerivativeRepresentative_selectedRestart_le_unheatedDerivativeMass
            hν U₀ hA hU₀ ht htR.le hlag i a x

      rw [hFEq]
      dsimp only [bound, B]

      calc
        ‖Q‖
            ≤
          ‖Q - T‖ + ‖T‖ := by
            have hAlg :
                Q = (Q - T) + T := by
              abel
            calc
              ‖Q‖ = ‖(Q - T) + T‖ :=
                congrArg norm hAlg
              _ ≤ ‖Q - T‖ + ‖T‖ :=
                norm_add_le _ _
        _ ≤
          h3FourierFirstDerivativeL1Coefficient * ‖ea‖ + J :=
          add_le_add hMoveOne hFixed
        _ ≤
          h3FourierFirstDerivativeL1Coefficient * ‖ea‖ + J + ‖E‖ := by
          exact le_add_of_nonneg_right (norm_nonneg E)

  have hBoundInt :
      Integrable
        bound
        μ := by
    dsimp only [bound, μ]
    change
      IntegrableOn
        (fun _u : ℝ => B)
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
    dsimp only [F, E, W, ea]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR hu i a x

  have hMain :
      Tendsto
        (fun h : ℝ =>
          ∫ u : ℝ, F h u ∂μ)
        (𝓝[Set.Ici (0 : ℝ)] 0)
        (𝓝
          (∫ _u : ℝ, E ∂μ)) := by
    exact
      tendsto_integral_filter_of_dominated_convergence
        (μ := μ)
        (l := (𝓝[Set.Ici (0 : ℝ)] 0))
        (F := F)
        (f := fun _u : ℝ => E)
        (bound := bound)
        hFMeas
        hBoundAE
        hBoundInt
        hLim

  have hPathEq :
      (fun h : ℝ =>
        ∫ u : ℝ, F h u ∂μ)
        =
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshFirstFrechetRescaledIntegrand
            ν t h W i a x u) := by
    funext h
    dsimp only [F, μ]
    rw [
      intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ]
    rw [← restrict_Ioo_eq_restrict_Ioc]

  have hLimitEq :
      (∫ _u : ℝ, E ∂μ) = E := by
    dsimp only [μ]
    have hConst :
        (∫ u in (0 : ℝ)..1, E) = E := by
      simp
    rw [
      intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)
    ] at hConst
    rw [← restrict_Ioo_eq_restrict_Ioc] at hConst
    exact hConst

  rw [hPathEq, hLimitEq] at hMain
  dsimp only [E, ea, W] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
