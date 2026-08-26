import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Second.Endpoint.Quarter.Mild.Local

/-!
# Quarter-Hölder endpoint forcing for the selected restart path

`Quarter.Mild.Local` closes the local terminal quarter-Hölder modulus of the
actual Banach-selected mild path.  The generic bilinear transfer theorem in
`Endpoint.Quarter` then turns that path modulus into the exact `L¹` endpoint
forcing modulus consumed by the second-Duhamel cancellation estimate.

This file removes the last abstract path-Hölder hypothesis from the nonlinear
forcing side on every positive terminal interval inside the canonical restart
radius.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval

noncomputable section

/-- Explicit local quarter-Hölder coefficient for the diagonal nonlinear
forcing along the selected restart path. -/
noncomputable def h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
    (ν A a t : ℝ) : ℝ :=
  4 * h3NonlinearForcingL1Coefficient * A *
    h3MildQuarterSelectedRestartLocalCoefficient ν A a t

/-- The selected local forcing coefficient is nonnegative on the natural
nonnegative parameter range. -/
theorem h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
    {ν A a t : ℝ}
    (hν : 0 ≤ ν)
    (hA : 0 ≤ A)
    (ht : 0 ≤ t) :
    0 ≤ h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t := by
  have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
    h3NonlinearForcingL1Coefficient_nonneg
  have hL : 0 ≤ h3MildQuarterSelectedRestartLocalCoefficient ν A a t :=
    h3MildQuarterSelectedRestartLocalCoefficient_nonneg hν hA ht
  unfold h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
  positivity

/-- On every positive terminal interval inside the canonical restart radius,
the raw diagonal nonlinear forcing of the selected mild path satisfies the
quarter-Hölder `L¹` endpoint condition required by the second-Duhamel
cancellation layer. -/
theorem h3NonlinearForcingEndpointQuarterHolderL1On_selectedRestart
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
    H3NonlinearForcingEndpointQuarterHolderL1On
      W W a t
      (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient ν A a t)
      i := by
  have ht0 : 0 ≤ t := (lt_trans ha hat).le

  have hL :
      0 ≤ h3MildQuarterSelectedRestartLocalCoefficient ν A a t :=
    h3MildQuarterSelectedRestartLocalCoefficient_nonneg
      hν.le hA.le ht0

  have hHolder :=
    h3SpectralEndpointQuarterHolderOn_selectedRestart
      hν U₀ hA hU₀ ha hat htR

  have hForcing :=
    h3NonlinearForcingEndpointQuarterHolderL1On_selectedRestart_of_path
      hν U₀ hA hU₀ ha.le hat.le htR hL hHolder i

  simpa only [h3NonlinearForcingQuarterSelectedRestartLocalCoefficient]
    using hForcing

end

end Euclidean
end Bridge
end PrimeTensor
