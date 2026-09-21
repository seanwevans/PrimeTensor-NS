import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Quartic.Inverse.Frechet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Cubic.Third.Jet.Continuity

/-!
# Classicalization: time continuity of evaluated fourth Fréchet derivatives

`QuarticInverseFrechetContinuity` proves that, at every strict positive
interior restart time `s`, the evaluated fourth Fréchet derivative of the
complex representative of the spectral difference state

    W(r)_i - W(s)_i

has norm tending to zero as `r → s`.

This file converts that difference-state statement into ordinary time
continuity of every fixed fourth spatial Fréchet evaluation of the selected
complex representative.

No new estimate is required. Reconstruction is subtraction-linear, and at
positive selected times `SpatialRegularity` gives `C⁴` regularity. Mathlib's
`iteratedFDeriv_sub_apply` therefore identifies

    D⁴ Rep(W(r)-W(s))[m]
      =
    D⁴ Rep(W(r))[m] - D⁴ Rep(W(s))[m].

The resulting norm convergence is exactly the metric criterion for
`ContinuousAt`.

No heat-kernel, forcing, or Navier--Stokes estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationQuarticFourthFrechetTimeContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- The selected complex representative's evaluated fourth spatial Fréchet
derivative has difference norm tending to zero at every strict positive
interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fourthFrechet_eval_sub_norm_tendsto_zero
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 4 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Tendsto
      (fun r : ℝ =>
        ‖iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative (W r i))
            x m
          -
          iteratedFDeriv ℝ 4
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
          ‖iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative
              (W r i - W s i))
            x m‖)
        (𝓝 s)
        (𝓝 0) := by
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fourthFrechet_difference_eval_norm_tendsto_zero
        hν U₀ hA hU₀ hs hsR i x m

  have hInterval :
      Set.Ioo
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν A)
        ∈ 𝓝 s :=
    Ioo_mem_nhds hs hsR

  have hEventuallyEq :
      ∀ᶠ r in 𝓝 s,
        ‖iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (W r i - W s i))
          x m‖
          =
        ‖iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative (W r i))
            x m
          -
          iteratedFDeriv ℝ 4
            (h3SpectralScalarC1Representative (W s i))
            x m‖ := by
    filter_upwards [hInterval] with r hr

    have hrC4 :
        ContDiff ℝ 4
          (h3SpectralScalarC1Representative
            (W r i)) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
          4 hν U₀ hA hU₀ hr.1 hr.2.le i

    have hsC4 :
        ContDiff ℝ 4
          (h3SpectralScalarC1Representative
            (W s i)) := by
      dsimp only [W]
      exact
        h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_contDiff_nat
          4 hν U₀ hA hU₀ hs hsR.le i

    rw [
      h3SpectralScalarC1Representative_sub
        (W r i)
        (W s i)
    ]

    have hIter :=
      iteratedFDeriv_sub_apply
        (𝕜 := ℝ)
        (i := 4)
        (x := x)
        hrC4.contDiffAt
        hsC4.contDiffAt

    have hEval :=
      congrArg
        (fun T =>
          T m)
        hIter

    change
      ‖iteratedFDeriv ℝ 4
          (fun y : H3FourierPoint3 =>
            h3SpectralScalarC1Representative (W r i) y
              -
            h3SpectralScalarC1Representative (W s i) y)
          x m‖
        =
      ‖iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative (W r i))
          x m
        -
        iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative (W s i))
          x m‖

    exact congrArg norm hEval

  have hTarget :
      Tendsto
        (fun r : ℝ =>
          ‖iteratedFDeriv ℝ 4
              (h3SpectralScalarC1Representative (W r i))
              x m
            -
            iteratedFDeriv ℝ 4
              (h3SpectralScalarC1Representative (W s i))
              x m‖)
        (𝓝 s)
        (𝓝 0) :=
    hDifference.congr' hEventuallyEq

  simpa only [W] using hTarget

/-- Every fixed evaluation of the selected complex representative's fourth
spatial Fréchet derivative is time-continuous at every strict positive
interior restart time. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fourthFrechet_eval_continuousAt
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s < h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (x : H3FourierPoint3)
    (m : Fin 4 → H3FourierPoint3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ContinuousAt
      (fun r : ℝ =>
        iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative (W r i))
          x m)
      s := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let J : ℝ → ℂ :=
    fun r =>
      iteratedFDeriv ℝ 4
        (h3SpectralScalarC1Representative (W r i))
        x m

  have hNormSub :
      Tendsto
        (fun r : ℝ => ‖J r - J s‖)
        (𝓝 s)
        (𝓝 0) := by
    dsimp only [J]
    simpa only [W] using
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_C1Representative_fourthFrechet_eval_sub_norm_tendsto_zero
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
        iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ r i))
          x m)
      (𝓝 s)
      (𝓝
        (iteratedFDeriv ℝ 4
          (h3SpectralScalarC1Representative
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ s i))
          x m))

  simpa only [J, W] using hJ

end
end Euclidean
end Bridge
end PrimeTensor
