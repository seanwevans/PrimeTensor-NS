import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Bridge

/-!
# Transfer of the quarter old-history bound to the standard Duhamel integrand

`Quarter.Duhamel.History.Bridge` identifies the custom selected positive-lag
kernel difference with the ordinary heat increment of the retarded Duhamel
integrand on the open history interval.  Since the two endpoint values are
irrelevant to the Bochner interval integral, the integrated bound from
`Quarter.Duhamel.History.Integral` transfers verbatim to the standard
integrand difference.

This leaves no custom kernel in the old-history estimate.  The next rung can
commute the heat CLM through the integral and identify this quantity with the
old-history contribution to the actual Duhamel time increment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- The integral of the selected old-history kernel difference is exactly the
integral of the heat increment of the standard Duhamel integrand. -/
theorem h3DuhamelQuarterSelectedHistoryKernelDifference_integral_eq_duhamelIntegrandDifference
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
        h3DuhamelQuarterSelectedHistoryKernelDifference
          ν hν U₀ A hA hU₀ t h s)
      =
    ∫ s in (0 : ℝ)..t,
      h3SpectralVelocityHeatApplyNN ν hν.le h
          (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s) -
        h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s := by
  dsimp only
  exact
    intervalIntegral.integral_congr_Ioo_of_le
      ht
      (h3DuhamelQuarterSelectedHistoryKernelDifference_eqOn_duhamelIntegrandDifference
        hν U₀ hA hU₀ h)

/-- The normalized quarter-power old-history bound, now stated directly for
the ordinary retarded Duhamel integrand. -/
theorem norm_h3DuhamelQuarterSelectedHistory_duhamelIntegrandDifference_integral_le
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
    ‖∫ s in (0 : ℝ)..t,
        h3SpectralVelocityHeatApplyNN ν hν.le h
            (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s) -
          h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s‖
      ≤
    4 * h3DuhamelQuarterHistoryPowerCoefficient
          ν (2 * A) (2 * A) *
      (h : ℝ) ^ ((1 : ℝ) / 4) *
      t ^ ((1 : ℝ) / 4) := by
  dsimp only
  calc
    ‖∫ s in (0 : ℝ)..t,
        h3SpectralVelocityHeatApplyNN ν hν.le h
            (h3SpectralFinHeatLerayDuhamelIntegrand
              ν t hν
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀)
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀) s) -
          h3SpectralFinHeatLerayDuhamelIntegrand
            ν t hν
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀)
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀) s‖
        =
      ‖∫ s in (0 : ℝ)..t,
          h3DuhamelQuarterSelectedHistoryKernelDifference
            ν hν U₀ A hA hU₀ t h s‖ := by
          rw [h3DuhamelQuarterSelectedHistoryKernelDifference_integral_eq_duhamelIntegrandDifference
            hν U₀ hA hU₀ ht h]
    _ ≤
      4 * h3DuhamelQuarterHistoryPowerCoefficient
            ν (2 * A) (2 * A) *
        (h : ℝ) ^ ((1 : ℝ) / 4) *
        t ^ ((1 : ℝ) / 4) := by
          exact
            norm_h3DuhamelQuarterSelectedHistoryKernelDifference_integral_le
              hν U₀ hA hU₀ ht h

end

end Euclidean
end Bridge
end PrimeTensor
