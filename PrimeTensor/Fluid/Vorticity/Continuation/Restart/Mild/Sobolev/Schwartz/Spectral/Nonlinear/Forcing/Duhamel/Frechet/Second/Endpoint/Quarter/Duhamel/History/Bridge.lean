import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Duhamel.History.Integral

/-!
# Bridge from the selected old-history kernel to the Duhamel integrand

`Quarter.Duhamel.History.Integral` controls the interval integral of the
selected positive-lag kernel difference.  This file identifies that custom
kernel pointwise with the ordinary retarded Duhamel integrand before the
terminal endpoint.

For every strict history time `s < t`,

    Δ_h K_{t-s}(W(s),W(s))
      = H_h I_t(s) - I_t(s),

where `I_t` is the standard heat--Leray Duhamel integrand.  The `EqOn` form is
the exact interface needed to replace the custom old-history integral by the
corresponding difference of standard Duhamel integrands on `0..t`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

/-- On every strict old-history time, the selected kernel difference is
exactly the heat increment of the standard retarded Duhamel integrand. -/
theorem h3DuhamelQuarterSelectedHistoryKernelDifference_eq_duhamelIntegrandDifference
    {ν A t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (h : NNReal)
    (hst : s < t) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    h3DuhamelQuarterSelectedHistoryKernelDifference
        ν hν U₀ A hA hU₀ t h s
      =
    h3SpectralVelocityHeatApplyNN ν hν.le h
        (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s) -
      h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s := by
  dsimp only
  simp only [
    h3DuhamelQuarterSelectedHistoryKernelDifference,
    h3SpectralFinHeatLerayDuhamelIntegrand,
    dif_pos hst,
    dif_pos (sub_pos.mpr hst)
  ]

/-- `EqOn` packaging of the old-history pointwise bridge on the open interval
`(0,t)`, ready for `intervalIntegral.integral_congr_Ioo_of_le`. -/
theorem h3DuhamelQuarterSelectedHistoryKernelDifference_eqOn_duhamelIntegrandDifference
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (h : NNReal) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    Set.EqOn
      (h3DuhamelQuarterSelectedHistoryKernelDifference
        ν hν U₀ A hA hU₀ t h)
      (fun s =>
        h3SpectralVelocityHeatApplyNN ν hν.le h
            (h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s) -
          h3SpectralFinHeatLerayDuhamelIntegrand ν t hν W W s)
      (Set.Ioo (0 : ℝ) t) := by
  dsimp only
  intro s hs
  exact
    h3DuhamelQuarterSelectedHistoryKernelDifference_eq_duhamelIntegrandDifference
      hν U₀ hA hU₀ h hs.2

end

end Euclidean
end Bridge
end PrimeTensor
