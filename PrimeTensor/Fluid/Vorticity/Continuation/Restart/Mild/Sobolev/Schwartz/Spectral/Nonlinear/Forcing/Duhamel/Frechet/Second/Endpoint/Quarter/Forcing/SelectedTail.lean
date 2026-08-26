import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedIntegral

/-!
# Selected quarter-Hölder forcing: canonical half-tail budget

`Forcing.SelectedIntegral` controls the quarter-cancelled second Fourier
moment on every positive terminal interval `a..t`.  For the positive-time
second-derivative bootstrap it is useful to choose the split point once and
for all.

This file fixes the canonical split `a = t / 2`.  When `t > 0`, the terminal
tail `t/2..t` is therefore covered by the selected quarter-cancellation
estimate, while every source time in the complementary head `0..t/2` has
heat lag at least `t/2`.

Thus the endpoint-singular and positive-lag pieces are now separated by one
concrete deterministic split.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the old head `s ≤ t/2`, the retarded heat lag is uniformly bounded
below by `t/2`. -/
theorem h3Quarter_halfTime_le_retardedLag
    {t s : ℝ}
    (hs : s ≤ t / 2) :
    t / 2 ≤ t - s := by
  linarith

/-- The selected quarter-cancelled second-moment tail has an explicit budget
on the canonical terminal half-interval `t/2..t`. -/
theorem norm_h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_intervalIntegral_le_quarter_selectedRestart_halfTail
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
    ‖∫ s in (t / 2)..t,
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)‖
      ≤
    12 * ν⁻¹ *
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (t / 2) t *
        (t - t / 2) ^ ((1 : ℝ) / 4) := by
  have htHalfPos : 0 < t / 2 := by
    exact div_pos ht (by norm_num)

  have htHalfLt : t / 2 < t := by
    linarith

  exact
    norm_h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_intervalIntegral_le_quarter_selectedRestart
      hν U₀ hA hU₀ htHalfPos htHalfLt htR i

end

end Euclidean
end Bridge
end PrimeTensor
