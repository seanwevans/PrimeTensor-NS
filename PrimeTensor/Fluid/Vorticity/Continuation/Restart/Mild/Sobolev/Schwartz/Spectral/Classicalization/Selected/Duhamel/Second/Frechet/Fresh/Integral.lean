import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Duhamel.Second.Frechet.Fresh.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Second.Coordinate.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Classicalization: second-Fréchet fresh-tail fixed-domain integral

The rescaled second-Fréchet fresh integrand now converges pointwise on
`u ∈ (0,1)` to the instantaneous selected forcing Hessian coordinate.

This file supplies the remaining fixed-domain dominated-convergence step.

Put

    M(r) = ∫ |ξ|² |N̂(W(r),W(r)) - N̂(W(t),W(t))|.

The selected forcing second-moment continuity theorem gives `M(r) → 0`.
Hence, near `t`, `M(r) < 1`.  For sufficiently small nonnegative `h`,
all points `t + h u`, `u ∈ [0,1]`, stay in that neighborhood and remain
inside the restart interval.

The moving-state contribution is then bounded by `(2π)^2`.  The frozen-state
positive-lag Hessian coordinate is uniformly bounded by `(2π)^2` times the
unheated radial second Fourier moment.  These two bounds give a constant
dominator on the unit interval.

Dominated convergence therefore turns the pointwise fresh-integrand limit into
the actual fixed-domain fresh quotient limit.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelSecondFrechetFreshIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- At a selected positive time, positive heat lag cannot increase the
pointwise mixed second-coordinate reconstruction beyond `(2π)^2` times the
unheated radial second Fourier mass. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_le_unheatedSecondMoment
    {ν A t τ : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hτ : 0 < τ)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
        ν τ (W t) (W t) i a b x‖
      ≤
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖) := by
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

  have hHeat2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖heated ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [heated]
    exact
      h3RawFinLerayOuterProductDivergenceHeatRepresentative_moment_integrable
        hν hτ (W t) (W t) i 2 (by norm_num)

  have hRaw2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 2 * ‖raw ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [raw, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_secondMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖heated ξ‖
          ≤
        ‖ξ‖ ^ 2 * ‖raw ξ‖ := by
    intro ξ
    have hHeat :
        ‖h3HeatFourierSymbol ν τ ξ‖ ≤ 1 :=
      norm_h3HeatFourierSymbol_le_one hν.le hτ.le ξ
    dsimp only [heated, raw]
    unfold h3RawFinLerayOuterProductDivergenceHeatRepresentative
    rw [norm_mul]
    exact
      mul_le_mul_of_nonneg_left
        (by
          calc
            ‖h3HeatFourierSymbol ν τ ξ‖ *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖
                ≤
              1 *
                ‖h3RawFinLerayOuterProductDivergence
                  (W t) (W t) i ξ‖ :=
              mul_le_mul_of_nonneg_right hHeat (norm_nonneg _)
            _ =
              ‖h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖ := by
              rw [one_mul])
        (by positivity)

  have hMassLe :
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖heated ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 * ‖raw ξ‖ := by
    exact
      integral_mono_ae
        hHeat2
        hRaw2
        (Filter.Eventually.of_forall hPoint)

  have hBase :=
    norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_le_secondMoment
      hν hτ (W t) (W t) i a b x

  have hCoeff0 :
      0 ≤ (2 * Real.pi) ^ 2 := by
    positivity

  exact
    hBase.trans
      (mul_le_mul_of_nonneg_left hMassLe hCoeff0)

/-- The selected rescaled second-Fréchet fresh integral converges from the
right to the instantaneous forcing Hessian coordinate. -/
theorem tendsto_intervalIntegral_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_selectedRestart_zero_right
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (i a b : Fin 3)
    (x : H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun h : ℝ =>
        ∫ u in (0 : ℝ)..1,
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
            ν t h W i a b x u)
      (𝓝[Set.Ici (0 : ℝ)] 0)
      (𝓝
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
          ])) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let E : ℂ :=
    iteratedFDeriv ℝ 2
      (h3RawFinLerayOuterProductDivergenceC0Representative
        (W t) (W t) i)
      x
      ![
        h3FourierAxisDirection (h3AxisOfFin3 a),
        h3FourierAxisDirection (h3AxisOfFin3 b)
      ]

  let M : ℝ → ℝ :=
    fun r =>
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
                (W r) (W r) i ξ
              -
            h3RawFinLerayOuterProductDivergence
                (W t) (W t) i ξ‖

  let J : ℝ :=
    (2 * Real.pi) ^ 2 *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ‖)

  let B : ℝ :=
    (2 * Real.pi) ^ 2 + J + ‖E‖

  let μ : Measure ℝ :=
    volume.restrict (Set.Ioo (0 : ℝ) 1)

  let F : ℝ → ℝ → ℂ :=
    fun h u =>
      h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
        ν t h W i a b x u

  let bound : ℝ → ℝ :=
    fun _u => B

  have hWcont :
      Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hMassBase :
      Tendsto M (𝓝 t) (𝓝 0) := by
    dsimp only [M, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_differenceSecondMass_tendsto_zero
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
    positivity

  have hCoeffNonneg :
      0 ≤ (2 * Real.pi) ^ 2 := by
    positivity

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
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        simp only [zero_mul, add_zero, sub_self]
        rw [
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
            hν U₀ hA hU₀ ht htR.le i a b x
        ]
      rw [hEq]
      exact continuous_const.aestronglyMeasurable

    · have hhpos :
          0 < h :=
        lt_of_le_of_ne hh (Ne.symm hh0)

      let P : ℝ → ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
          ν (t + h) W W i a b x

      have hP :
          ContinuousOn
            P
            (Set.Ioo (0 : ℝ) (t + h)) := by
        dsimp only [P, W]
        exact
          continuousOn_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath_selectedRestart_Ioo
            hν U₀ hA hU₀ i a b x

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
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
            ν t h W i a b x u

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
        h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
      ]
      unfold
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
      simp only [zero_mul, add_zero, sub_self]
      rw [
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_zero_eq_selectedRestart_iteratedFDeriv
          hν U₀ hA hU₀ ht htR.le i a b x
      ]
      dsimp only [E]
      have hLeft :
          0 ≤ (2 * Real.pi) ^ 2 + J := by
        positivity
      linarith [norm_nonneg
        (iteratedFDeriv ℝ 2
          (h3RawFinLerayOuterProductDivergenceC0Representative
            (W t) (W t) i)
          x
          ![
            h3FourierAxisDirection (h3AxisOfFin3 a),
            h3FourierAxisDirection (h3AxisOfFin3 b)
          ])]

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
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν (h * (1 - u))
          (W (t + h * u))
          (W (t + h * u))
          i a b x

      let T : ℂ :=
        h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative
          ν (h * (1 - u))
          (W t) (W t)
          i a b x

      have hFEq :
          F h u = Q := by
        dsimp only [F, Q]
        rw [
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_eq_secondCoordinateRetardedPath
        ]
        unfold
          h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRetardedPath
        rw [hLagEq]

      have hMove :
          ‖Q - T‖
            ≤
          (2 * Real.pi) ^ 2 *
            M (t + h * u) := by
        dsimp only [Q, T, M, W, R] at hri ⊢
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_sub_le_differenceSecondMass
            hν U₀ hA hU₀
            hri.1 hri.2.le
            ht htR.le
            hlag
            i a b x

      have hMoveOne :
          ‖Q - T‖
            ≤
          (2 * Real.pi) ^ 2 := by
        calc
          ‖Q - T‖
              ≤
            (2 * Real.pi) ^ 2 *
              M (t + h * u) :=
            hMove
          _ ≤
            (2 * Real.pi) ^ 2 * 1 := by
              exact
                mul_le_mul_of_nonneg_left
                  hMlt.le
                  hCoeffNonneg
          _ = (2 * Real.pi) ^ 2 := by
              ring

      have hFixed :
          ‖T‖ ≤ J := by
        dsimp only [T, J, W]
        exact
          norm_h3RawFinLerayOuterProductDivergenceHeatSecondCoordinateRepresentative_selectedRestart_le_unheatedSecondMoment
            hν U₀ hA hU₀ ht htR.le hlag i a b x

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
          (2 * Real.pi) ^ 2 + J :=
          add_le_add hMoveOne hFixed
        _ ≤
          (2 * Real.pi) ^ 2 + J + ‖E‖ := by
          exact le_add_of_nonneg_right (norm_nonneg E)

  have hBoundInt :
      Integrable bound μ := by
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
    dsimp only [F, E, W]
    exact
      tendsto_h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand_selectedRestart_zero_right
        hν U₀ hA hU₀ ht htR hu i a b x

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
          h3RawFinLerayOuterProductDivergenceHeatFreshSecondFrechetRescaledIntegrand
            ν t h W i a b x u) := by
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
  dsimp only [E, W] at hMain
  exact hMain

end

end Euclidean
end Bridge
end PrimeTensor
