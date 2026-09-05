import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Frechet.Continuity

/-!
# Classicalization: evaluation of the cubic Frechet continuity

`CubicFrechetContinuity` proves convergence to zero of the operator norm of the
complete third Frechet derivative of the Fourier transform of a selected
difference state.

This file performs only the multilinear evaluation step.  For any fixed triple
of spatial directions `m : Fin 3 → H3FourierPoint3`, the norm of the evaluated
third derivative is bounded by the operator norm times

    ∏ k, ‖m k‖.

Hence the evaluated derivative also tends to zero.

The next classicalization increment can therefore focus entirely on geometric
identification: inverse-Fourier negation, the `WithLp.toLp` spatial carrier map,
and the three axis directions appearing in the ordered `spatial3.d` jet.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationCubicFrechetEvaluationContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Evaluation at a fixed triple of directions preserves convergence to zero
when the operator norm of a third continuous multilinear map converges to
zero. -/
theorem thirdContinuousMultilinearMap_eval_norm_tendsto_zero
    {F :
      ℝ →
        ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 3 => H3FourierPoint3)
          ℂ}
    {s : ℝ}
    (hF :
      Tendsto
        (fun r : ℝ => ‖F r‖)
        (𝓝 s)
        (𝓝 0))
    (m : Fin 3 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ => ‖F r m‖)
      (𝓝 s)
      (𝓝 0) := by
  let K : ℝ := ∏ k : Fin 3, ‖m k‖

  have hK0 : 0 ≤ K := by
    dsimp only [K]
    exact Finset.prod_nonneg (fun k _ => norm_nonneg (m k))

  have hScaled :
      Tendsto
        (fun r : ℝ => ‖F r‖ * K)
        (𝓝 s)
        (𝓝 0) := by
    have hConst :
        Tendsto
          (fun _ : ℝ => K)
          (𝓝 s)
          (𝓝 K) :=
      tendsto_const_nhds
    have hMul := hF.mul hConst
    simpa only [zero_mul] using hMul

  refine tendsto_order.2 ⟨?_, ?_⟩

  · intro c hc
    exact Filter.Eventually.of_forall (fun r =>
      lt_of_lt_of_le hc (norm_nonneg _))

  · intro ε hε

    have hScaledEventually :
        ∀ᶠ r in 𝓝 s, ‖F r‖ * K < ε :=
      (tendsto_order.1 hScaled).2 ε hε

    filter_upwards [hScaledEventually] with r hr

    have hEval :
        ‖F r m‖ ≤ ‖F r‖ * K := by
      dsimp only [K]
      exact (F r).le_opNorm m

    exact lt_of_le_of_lt hEval hr

/-- The third Frechet derivative of the selected raw-Fourier difference state,
evaluated on any fixed triple of Fourier-space directions, tends to zero at
every strict positive interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_thirdFrechet_difference_eval_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 3 → H3FourierPoint3) :
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 3
          (FourierTransform.fourier
            (h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r i
                -
                h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ s i)))
          x m‖)
      (𝓝 s)
      (𝓝 0) := by
  let F :
      ℝ →
        ContinuousMultilinearMap
          ℝ
          (fun _ : Fin 3 => H3FourierPoint3)
          ℂ :=
    fun r =>
      iteratedFDeriv ℝ 3
        (FourierTransform.fourier
          (h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ r i
              -
              h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ s i)))
        x

  have hOperator :
      Tendsto
        (fun r : ℝ => ‖F r‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [F] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fourier_thirdFrechet_difference_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x

  have hEval :=
    thirdContinuousMultilinearMap_eval_norm_tendsto_zero
      hOperator m

  simpa only [F] using hEval

end
end Euclidean
end Bridge
end PrimeTensor
