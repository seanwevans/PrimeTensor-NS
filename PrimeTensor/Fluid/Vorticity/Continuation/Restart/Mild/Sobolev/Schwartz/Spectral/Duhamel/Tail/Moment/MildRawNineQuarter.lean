import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildNineQuarter
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildRawSecond

/-!
# Canonical raw Fourier nine-quarter moment of the selected mild state

`MildNineQuarter` proves the `9/4` raw Fourier moment on the quotient-safe
`L²` package obtained by coordinate projection and exact H³ deweighting.

The nonlinear forcing layer, however, is written in terms of the canonical
pointwise representative

    h3SpectralScalarRawFourier (W t i).

`MildRawSecond` already closes the representation bridge between that canonical
raw Fourier function and the named deweighted `L²` package.

This file simply transports the newly established `9/4` weighted integrability
across the same almost-everywhere identity.  No new estimate is introduced.

The result is exactly the pointwise input needed to propagate the `9/4` moment
through `h3RawProductConvolution`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedMildRawNineQuarter
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical selected mild raw Fourier `9/4` density agrees almost
everywhere with the density of the named raw Fourier `L²` package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineQuarterMoment_ae_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineQuarterWeight ξ *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineQuarterWeight ξ *
        ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ t i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := t)
      hν U₀ hA hU₀ i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Every selected positive-time coordinate has an integrable `9/4` moment in
the canonical raw Fourier representative used by the nonlinear forcing layer. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMoment_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  exact hNamed.congr hEq.symm

end
end Euclidean
end Bridge
end PrimeTensor
