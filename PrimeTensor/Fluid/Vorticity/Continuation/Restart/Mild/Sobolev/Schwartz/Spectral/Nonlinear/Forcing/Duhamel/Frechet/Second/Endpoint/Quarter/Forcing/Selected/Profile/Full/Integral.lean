import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Profile.Time.Integrable

/-!
# Full selected second-moment Duhamel-time budget

The selected second-moment profile is now genuinely interval-integrable on
`0..t`.  Therefore the old-head / terminal-half split can finally be collapsed
with the actual adjacent-interval integral identity, rather than merely
bounding two unrelated Lean interval integrals.

Combining that identity with the already-closed canonical two-piece unsplit
budget gives a single bound for the real full `0..t` second-moment source-time
integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedProfileFullIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine full selected second-moment source-time integral is bounded by
the canonical selected restart budget. -/
theorem norm_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_intervalIntegral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ‖∫ s in (0 : ℝ)..t,
        h3NonlinearForcingHeatSecondMomentProfile ν t W i s‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let P : ℝ → ℝ :=
    h3NonlinearForcingHeatSecondMomentProfile ν t W i

  have hHead :
      IntervalIntegrable P volume 0 (t / 2) := by
    dsimp only [P, W]
    exact
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfHead_intervalIntegrable
        hν U₀ hA hU₀ ht i

  have hTail :
      IntervalIntegrable P volume (t / 2) t := by
    dsimp only [P, W]
    exact
      h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_halfTail_intervalIntegrable
        hν U₀ hA hU₀ ht htR i

  have hSplit :
      (∫ s in (0 : ℝ)..t, P s)
        =
      (∫ s in (0 : ℝ)..(t / 2), P s) +
        ∫ s in (t / 2)..t, P s := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        hHead hTail).symm

  have hBudget :
      ‖∫ s in (0 : ℝ)..(t / 2), P s‖ +
        ‖∫ s in (t / 2)..t, P s‖
        ≤
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
    dsimp only [P, W]
    exact
      norm_h3NonlinearForcingHeatSecondMomentProfile_selectedRestart_head_add_halfTail_le
        hν U₀ hA hU₀ ht htR i

  change
    ‖∫ s in (0 : ℝ)..t, P s‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t

  rw [hSplit]

  exact
    (norm_add_le
      (∫ s in (0 : ℝ)..(t / 2), P s)
      (∫ s in (t / 2)..t, P s)).trans
      hBudget

end

end Euclidean
end Bridge
end PrimeTensor
