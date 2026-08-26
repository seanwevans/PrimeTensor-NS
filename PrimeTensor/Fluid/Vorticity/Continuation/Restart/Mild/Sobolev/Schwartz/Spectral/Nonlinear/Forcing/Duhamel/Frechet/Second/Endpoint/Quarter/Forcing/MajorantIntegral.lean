import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SecondMoment

/-!
# Selected quarter-Hölder forcing: integrated cancellation majorant

The selected-path fixed-lag second-moment estimate is now pointwise dominated
by the universal quarter-cancellation kernel

    (3 * ν⁻¹ * K) * (t - s)^(-3/4).

This file evaluates that scalar kernel on a general positive-length terminal
interval.  The `-3/4` singularity contributes exactly the finite factor
`4 * (t-a)^(1/4)`, so the complete endpoint budget is

    12 * ν⁻¹ * K * (t-a)^(1/4).

This is the scalar integration identity needed to pass from the selected
fixed-lag second-moment bound to an integrated endpoint estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

/-- Exact integral of the quarter-cancellation second-derivative majorant on
an arbitrary terminal interval. -/
theorem h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_integral_on
    {ν a t K : ℝ}
    (_hat : a ≤ t) :
    (∫ s in a..t,
        h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
          ν t K s)
      =
    12 * ν⁻¹ * K * (t - a) ^ ((1 : ℝ) / 4) := by
  have hReverse :
      (∫ s in a..t,
          (t - s) ^ (-(3 : ℝ) / 4))
        =
      ∫ q in (0 : ℝ)..(t - a),
          q ^ (-(3 : ℝ) / 4) := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (a := a)
        (b := t)
        (fun q : ℝ => q ^ (-(3 : ℝ) / 4))
        t)

  have hPower :
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(3 : ℝ) / 4))
        =
      4 * (t - a) ^ ((1 : ℝ) / 4) := by
    calc
      (∫ q in (0 : ℝ)..(t - a),
          q ^ (-(3 : ℝ) / 4))
          =
        ((t - a) ^ ((-(3 : ℝ) / 4) + 1) -
            (0 : ℝ) ^ ((-(3 : ℝ) / 4) + 1)) /
          (((-(3 : ℝ) / 4) + 1)) := by
            exact
              integral_rpow
                (a := (0 : ℝ))
                (b := t - a)
                (r := (-(3 : ℝ) / 4))
                (Or.inl (by norm_num))
      _ = 4 * (t - a) ^ ((1 : ℝ) / 4) := by
            rw [show (-(3 : ℝ) / 4) + 1 = (1 : ℝ) / 4 by ring]
            rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 4 ≠ 0)]
            ring

  unfold h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
  rw [intervalIntegral.integral_const_mul]
  rw [hReverse, hPower]
  ring

end

end Euclidean
end Bridge
end PrimeTensor
