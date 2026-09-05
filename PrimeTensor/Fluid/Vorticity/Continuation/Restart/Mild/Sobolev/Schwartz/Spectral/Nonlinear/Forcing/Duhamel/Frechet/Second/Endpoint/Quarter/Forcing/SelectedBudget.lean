import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedSplit
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Frozen.Fubini

/-!
# Selected quarter-Hölder forcing: complete split budget

The canonical second-moment decomposition now has three independently closed
pieces:

* the uncancelled old head on `0..t/2`;
* the quarter-cancelled terminal tail on `t/2..t`;
* the forcing frozen at terminal time on `t/2..t`.

`Forcing.SelectedSplit` bounds the first two pieces together, while
`Forcing.SelectedFrozenFubini` puts the frozen piece in the same
source-time-outer / frequency-inner order used by the second-Duhamel formula.

This file packages those estimates into one scalar budget.  It introduces no
new analytic estimate; its purpose is to give the downstream recombination
step one closed quantity to target.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedBudget
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Complete scalar budget for the old head, quarter-cancelled terminal tail,
and frozen terminal forcing contribution. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget
    (ν A t : ℝ) : ℝ :=
  h3NonlinearForcingQuarterSelectedRestartSplitSecondMomentBudget ν A t +
    (((2 * Real.pi) ^ 2 * ν)⁻¹) *
      (4 * h3NonlinearForcingL1Coefficient * A ^ 2)

/-- The three pieces of the canonical selected second-moment decomposition are
bounded by the complete selected restart budget. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_selectedSplit_add_frozen_halfTail_le_quarter_selectedRestart
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
    ‖∫ s in (0 : ℝ)..(t / 2),
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)‖ +
      ‖∫ s in (t / 2)..t,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)‖ +
      (∫ s in (t / 2)..t,
        ∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ‖)
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  dsimp only

  have hSplit :=
    norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_head_add_endpointDifference_tail_intervalIntegrals_le_quarter_selectedRestart
      hν U₀ hA hU₀ ht htR i

  have hFrozen :=
    h3RawFinLerayOuterProductDivergenceHeat_frozenSecondMoment_halfTail_time_frequencyIntegral_le_selectedRestart
      hν U₀ hA hU₀ ht i

  exact add_le_add hSplit hFrozen

end

end Euclidean
end Bridge
end PrimeTensor
