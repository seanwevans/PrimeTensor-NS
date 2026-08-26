import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedHeadBound

/-!
# Selected quarter-Hölder forcing: half-head majorant integral

`Forcing.SelectedHeadBound` gives a source-time-independent bound for the
second Fourier moment on the canonical head `0..t/2`.  This file packages
that constant as a scalar time majorant and records its interval
integrability and exact integral.

Thus the old head has the explicit budget

    (t / 2) * C_head(ν,A,t),

where `C_head` is the fixed positive-lag coefficient from `SelectedHeadBound`.
The next layer only has to transfer the pointwise selected head estimate
under the time integral.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

/-- Constant scalar majorant for the selected second-moment forcing on the
canonical old half-head. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
    (ν A t : ℝ) (_s : ℝ) : ℝ :=
  h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient ν A t

/-- The constant selected half-head second-moment majorant is interval
integrable on `0..t/2`. -/
theorem h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant_intervalIntegrable
    {ν A t : ℝ} :
    IntervalIntegrable
      (h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant ν A t)
      volume
      0
      (t / 2) := by
  unfold h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
  exact intervalIntegrable_const

/-- Exact integral of the constant selected half-head second-moment
majorant. -/
theorem h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant_integral
    {ν A t : ℝ} :
    (∫ s in (0 : ℝ)..(t / 2),
        h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
          ν A t s)
      =
    (t / 2) *
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
        ν A t := by
  unfold h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentMajorant
  simp

end

end Euclidean
end Bridge
end PrimeTensor
