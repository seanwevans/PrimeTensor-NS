import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedBudget
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected.Tail.Integral.Triangle

/-!
# Selected quarter-Hölder forcing: canonical unsplit split budget

The earlier selected budget was assembled from three pieces:

* the unsplit old head on `0..t/2`;
* the endpoint-cancelled terminal tail on `t/2..t`;
* the terminally frozen forcing on `t/2..t`.

`Forcing.SelectedTailIntegralTriangle` has now recombined the final two pieces
inside the actual unsplit terminal profile.  This file therefore packages the
canonical two-piece form of the same budget:

    ‖head unsplit integral‖ + ‖tail unsplit integral‖ ≤ selected budget.

No adjacent-interval identity is used here.  That identity requires genuine
time integrability of the full scalar profile, which is intentionally left to
the next measure-theoretic rung.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedUnsplitBudget
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The two actual unsplit pieces of the selected second-moment profile are
bounded by the same canonical budget previously assembled from the
head/cancelled/frozen decomposition. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_head_add_unsplit_halfTail_intervalIntegrals_le_quarter_selectedRestart
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
              h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ‖)‖
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  dsimp only

  have hHead :=
    norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_intervalIntegral_le_quarter_selectedRestart_halfHead
      hν U₀ hA hU₀ ht i

  have hTail :=
    norm_h3RawFinLerayOuterProductDivergenceHeat_secondMoment_unsplit_halfTail_intervalIntegral_le_quarter_selectedRestart
      hν U₀ hA hU₀ ht htR i

  have hSum := add_le_add hHead hTail

  have hBudgetEq :
      (t / 2) *
          h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
            ν A t +
        h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
          ν A t
        =
      h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
    unfold h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget
    unfold h3NonlinearForcingQuarterSelectedRestartSplitSecondMomentBudget
    unfold h3NonlinearForcingQuarterSelectedRestartUnsplitHalfTailSecondMomentBudget
    ring

  exact hSum.trans_eq hBudgetEq

end

end Euclidean
end Bridge
end PrimeTensor
