import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedHeadIntegral

/-!
# Selected quarter-Hölder forcing: canonical split budget

`Forcing.SelectedHeadIntegral` controls the uncancelled old half-head
`0..t/2`, while `Forcing.SelectedTail` controls the quarter-cancelled
terminal half `t/2..t`.

This file packages those two independently integrated estimates into one
canonical split budget.  No new analytic estimate is introduced here: the
point is to expose a single scalar quantity containing exactly the two pieces
that survive after the second-Duhamel interval is split at `t/2`.

The remaining terminal frozen-forcing contribution can then be handled as a
separate heat primitive, without mixing it back into the endpoint-singular
estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedSplit
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit scalar budget for the two already-integrated pieces of the
canonical second-moment split: the uncancelled old head and the
quarter-cancelled terminal tail. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartSplitSecondMomentBudget
    (ν A t : ℝ) : ℝ :=
  (t / 2) *
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
        ν A t +
    12 * ν⁻¹ *
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (t / 2) t *
      (t - t / 2) ^ ((1 : ℝ) / 4)

/-- The sum of the integrated old-head second moment and the integrated
quarter-cancelled terminal-tail second moment is bounded by the canonical
selected split budget. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_head_add_endpointDifference_tail_intervalIntegrals_le_quarter_selectedRestart
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
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartSplitSecondMomentBudget
      ν A t := by
  dsimp only

  have hHead :=
    norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_intervalIntegral_le_quarter_selectedRestart_halfHead
      hν U₀ hA hU₀ ht i

  have hTail :=
    norm_h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_intervalIntegral_le_quarter_selectedRestart_halfTail
      hν U₀ hA hU₀ ht htR i

  exact add_le_add hHead hTail

end

end Euclidean
end Bridge
end PrimeTensor
