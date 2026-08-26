import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Commute

/-!
# Quarter-power bound for the actual old Duhamel history increment

`Quarter.Duhamel.History.Transfer` bounded the interval of pointwise heat
increments, and `Quarter.Duhamel.History.Commute` identified that interval
with the heat increment of the Duhamel integral itself.  This file closes that
bridge and records the estimate in the form needed by the later Duhamel
restart decomposition:

    ‖H_h D_t(W,W) - D_t(W,W)‖
      ≤ 4 C_hist(ν,2A,2A) h^(1/4) t^(1/4).

No custom history kernel remains in the statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- The old-history part of the selected-path Duhamel increment is
quarter-Hölder under an additional heat step. -/
theorem norm_h3DuhamelQuarterSelectedHistory_heatDuhamelDifference_le
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
    ‖h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayDuhamel ν t hν W W) -
        h3SpectralFinHeatLerayDuhamel ν t hν W W‖
      ≤
    4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
      (h : ℝ) ^ ((1 : ℝ) / 4) *
      t ^ ((1 : ℝ) / 4) := by
  dsimp only

  have hEq :=
    h3DuhamelQuarterSelectedHistory_duhamelIntegrandDifference_integral_eq_heatDuhamelDifference
      hν U₀ hA hU₀ ht h

  have hBound :=
    norm_h3DuhamelQuarterSelectedHistory_duhamelIntegrandDifference_integral_le
      hν U₀ hA hU₀ ht h

  rw [← hEq]
  exact hBound

end

end Euclidean
end Bridge
end PrimeTensor
