import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.SelectedMajorantIntegral

/-!
# Selected quarter-Hölder forcing: almost-everywhere time majorization

The selected fixed-lag second-moment estimate is pointwise on the open
terminal interval `Ioo a t`, while the scalar quarter-cancellation majorant is
already interval-integrable there.

This file puts those two facts into the measure-theoretic form used by the
Bochner/integrability layer: the actual selected second-moment profile is
bounded almost everywhere on the restricted open interval, and the selected
majorant is integrable on that same open interval.

The endpoints are deliberately removed here.  They are irrelevant to the
time integral and this avoids manufacturing artificial endpoint estimates for
the singular cancellation kernel.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSelectedAEMajorant
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the open terminal interval, the selected-path second Fourier moment is
almost everywhere bounded by the explicit quarter-cancellation majorant. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart_ae
    {ν A a t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo a t)),
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖h3HeatFourierSymbol ν (t - s) ξ *
              (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
                h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)
        ≤
      h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
        ν t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)
        s := by
  dsimp only
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards with s hs
  exact
    h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart
      hν U₀ hA hU₀ ha hat htR hs i

/-- The selected quarter-cancellation scalar majorant is integrable on the
open terminal interval used by the endpoint estimate. -/
theorem h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_integrableOn_Ioo_selectedRestart
    {ν A a t : ℝ}
    (hat : a ≤ t) :
    IntegrableOn
      (h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
        ν t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t))
      (Set.Ioo a t)
      volume := by
  rw [
    ← integrableOn_Ioc_iff_integrableOn_Ioo,
    ← intervalIntegrable_iff_integrableOn_Ioc_of_le hat
  ]
  exact
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant_intervalIntegrable_selectedRestart

end

end Euclidean
end Bridge
end PrimeTensor
