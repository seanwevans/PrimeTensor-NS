import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Transfer
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Retarded.Integrability

/-!
# Commuting the quarter old-history increment through the Duhamel integral

`Quarter.Duhamel.History.Transfer` controls the interval integral of the heat
increment of the ordinary retarded Duhamel integrand.  This file identifies
that integral with the heat increment of the Duhamel integral itself.

The clean way to do this is to package the old-history increment as the single
continuous linear map

    H_h - I.

Then `ContinuousLinearMap.intervalIntegral_comp_comm` moves that whole map
through the Bochner interval integral in one step.  This avoids separately
proving interval integrability of the heat-transformed integrand merely to use
`intervalIntegral.integral_sub`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- The transferred old-history integral is exactly the heat increment of the
selected-path Duhamel term at the same terminal time. -/
theorem h3DuhamelQuarterSelectedHistory_duhamelIntegrandDifference_integral_eq_heatDuhamelDifference
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 ≤ t)
    (h : NNReal) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    (∫ s in (0 : ℝ)..t,
        h3SpectralVelocityHeatApplyNN ν hν.le h
            (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s) -
          h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s)
      =
    h3SpectralVelocityHeatApplyNN ν hν.le h
        (h3SpectralFinHeatLerayDuhamel ν t hν W W) -
      h3SpectralFinHeatLerayDuhamel ν t hν W W := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let I : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W

  let H : H3SpectralFinVectorState →L[ℝ] H3SpectralFinVectorState :=
    h3SpectralVelocityHeatCLM ν hν.le h

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀

  have hW : ∀ s : ℝ, ‖W s‖ ≤ 2 * A := by
    intro s
    dsimp only [W]
    exact
      norm_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension_le_twoA
        hν U₀ hA hU₀ s

  have h2A : 0 ≤ 2 * A := by
    positivity

  have hInt : IntervalIntegrable I volume 0 t := by
    dsimp only [I]
    exact
      h3SpectralFinHeatLerayDuhamelIntegrand_intervalIntegrable_of_continuous
        hν ht h2A h2A W W hWcont hWcont
        (fun s _hs => hW s)
        (fun s _hs => hW s)

  let D : H3SpectralFinVectorState →L[ℝ] H3SpectralFinVectorState :=
    H - ContinuousLinearMap.id ℝ H3SpectralFinVectorState

  have hComm := D.intervalIntegral_comp_comm hInt

  have hDifference :
      (∫ s in (0 : ℝ)..t, H (I s) - I s)
        =
      H (∫ s in (0 : ℝ)..t, I s) -
        ∫ s in (0 : ℝ)..t, I s := by
    simpa [D] using hComm

  unfold h3SpectralFinHeatLerayDuhamel
  simpa [I, H] using hDifference

end

end Euclidean
end Bridge
end PrimeTensor
