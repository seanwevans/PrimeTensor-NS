import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quintic.Inverse.Frechet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Fourth.Frechet.Time.Continuity

/-!
# Classicalization: time continuity of evaluated fifth Fréchet derivatives

`QuinticInverseFrechetContinuity` proves that, at every strict positive
interior restart time `s`, the evaluated fifth Fréchet derivative of the
complex representative of the spectral difference state

    W(r)_i - W(s)_i

has norm tending to zero as `r → s`.

This file converts that difference-state statement into ordinary time
continuity of every fixed fifth spatial Fréchet evaluation of the selected
complex representative.

No new estimate is required. Reconstruction is subtraction-linear, and at
positive selected times the existing spatial regularity gives `C⁵`
regularity. Mathlib's `iteratedFDeriv_sub_apply` therefore identifies

    D⁵ Rep(W(r)-W(s))[m]
      =
    D⁵ Rep(W(r))[m] - D⁵ Rep(W(s))[m].

The resulting norm convergence is exactly the metric criterion for
`ContinuousAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuinticFifthFrechetTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The selected complex representative's evaluated fifth spatial Fréchet
derivative has difference norm tending to zero at every strict positive
interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_eval_sub_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 5 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative (W r i))
            x m
          -
          iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative (W s i))
            x m‖)
      (𝓝 s)
      (𝓝 0) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hDifference :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative
              (W r i - W s i))
            x m‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x m

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative (W r i))
            x m
          -
          iteratedFDeriv ℝ 5
            (h3SpectralScalarC1Representative (W s i))
            x m‖ := by
    filter_upwards [hInterval] with r hr

    have hrC5 :
        ContDiff ℝ 5
          (h3SpectralScalarC1Representative
            (W r i)) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
          5 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsC5 :
        ContDiff ℝ 5
          (h3SpectralScalarC1Representative
            (W s i)) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
          5 hν U₀ hA hU₀ hs hsR.le i

    rw [
      h3SpectralScalarC1Representative_sub
        (W r i)
        (W s i)
    ]

    have hIter :=
      iteratedFDeriv_sub_apply
        (𝕜 := ℝ)
        (i := 5)
        (x := x)
        hrC5.contDiffAt
        hsC5.contDiffAt

    have hEval :=
      congrArg
        (fun T =>
          T m)
        hIter

    change
      ‖iteratedFDeriv ℝ 5
          (fun y : H3FourierPoint3 =>
            h3SpectralScalarC1Representative (W r i) y
              -
            h3SpectralScalarC1Representative (W s i) y)
          x m‖
        =
      ‖iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative (W r i))
          x m
        -
        iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative (W s i))
          x m‖

    exact congrArg norm hEval

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 5
              (h3SpectralScalarC1Representative (W r i))
              x m
            -
            iteratedFDeriv ℝ 5
              (h3SpectralScalarC1Representative (W s i))
              x m‖)
        (𝓝 s)
        (𝓝 0) :=
    hDifference.congr' hEventuallyEq

  simpa only [W] using hTarget

/-- Every fixed evaluation of the selected complex representative's fifth
spatial Fréchet derivative is time-continuous at every strict positive
interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_eval_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 5 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative (W r i))
          x m)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let J : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 5
        (h3SpectralScalarC1Representative (W r i))
        x m

  have hNormSub :
      Tendsto
        (fun r : ℝ => ‖J r - J s‖)
        (𝓝 s)
        (𝓝 0) := by
    dsimp only [J]
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fifthFrechet_eval_sub_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x m

  have hJ :
      Tendsto
        J
        (𝓝 s)
        (𝓝 (J s)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε

    have hEventually :
        ∀ᶠ r in 𝓝 s,
          ‖J r - J s‖ < ε :=
      (tendsto_order.1 hNormSub).2 ε hε

    filter_upwards [hEventually] with r hr

    simpa only [dist_eq_norm] using hr

  change
    Tendsto
      (fun r : ℝ =>
        iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ r i))
          x m)
      (𝓝 s)
      (𝓝
        (iteratedFDeriv ℝ 5
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s i))
          x m))

  simpa only [J, W] using hJ

end
end Euclidean
end Bridge
end PrimeTensor
