import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Forcing.Selected

/-!
# Selected quarter-Hölder forcing: second-moment endpoint bound

`Quarter.Forcing.Selected` supplies the exact local `L¹` quarter-Hölder
endpoint modulus of the diagonal nonlinear forcing along the Banach-selected
restart path.  The generic quarter-cancellation theorem can therefore be
specialized immediately to that path.

This file removes the forcing predicate from the fixed-lag second Fourier
moment estimate: every source time in the positive terminal interval is now
bounded directly by the integrable `(t-s)^(-3/4)` cancellation majorant with
the explicit selected-path coefficient.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

noncomputable local instance axisFintypeH3SchwartzQuarterForcingSecondMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Fixed-lag second-Fourier-moment endpoint cancellation for the actual
Banach-selected restart path. -/
theorem h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter_selectedRestart
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
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

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hHolder :
      H3NonlinearForcingEndpointQuarterHolderL1On
        W W a t
        (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)
        i := by
    dsimp only [W]
    exact
      h3NonlinearForcingEndpointQuarterHolderL1On_selectedRestart
        hν U₀ hA hU₀ ha hat htR i

  change
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3HeatFourierSymbol ν (t - s) ξ *
            (h3RawFinLerayOuterProductDivergence (W s) (W s) i ξ -
              h3RawFinLerayOuterProductDivergence (W t) (W t) i ξ)‖)
      ≤
    h3NonlinearForcingHeatSecondDerivativeQuarterCancellationMajorant
      ν t
      (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)
      s

  exact
    h3RawFinLerayOuterProductDivergenceHeat_endpointDifference_secondMoment_le_quarter
      hν W W i hs hHolder

end

end Euclidean
end Bridge
end PrimeTensor
