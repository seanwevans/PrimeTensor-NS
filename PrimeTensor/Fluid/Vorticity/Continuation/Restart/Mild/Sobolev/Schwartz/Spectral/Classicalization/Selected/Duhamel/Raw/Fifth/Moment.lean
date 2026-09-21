import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.Fifth.Duhamel.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.C1.Representative

/-!
# Classicalization: fifth moment of the named selected Duhamel raw amplitude

The sixth endpoint already proves the full fifth raw Fourier moment of the
selected Duhamel `L²` representative:

    ∫ |ξ|⁵ |D_raw,L²(t,ξ)| dξ < ∞.

The pointwise Duhamel reconstruction stack identifies that quotient-safe `L²`
representative almost everywhere with the explicit named amplitude

    h3SelectedDuhamelRawFourierAmplitude.

This file transports the fifth moment across that a.e. identification.

The resulting theorem is the exact input needed for the fifth-coordinate
inverse-Fourier reconstruction consumed by the order-three old-history
generator trace.

No new estimate or Fourier interchange is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelRawFifthMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit named selected Duhamel raw Fourier amplitude has an
integrable fifth radial moment at every strict positive time inside the
restart radius. -/
theorem h3SelectedDuhamelRawFourierAmplitude_fifthMoment_integrable
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
        ‖ξ‖ ^ 5 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hL2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 5 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fifthMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  refine hL2.congr ?_
  filter_upwards [hEq] with ξ hξ
  rw [hξ]

end

end Euclidean
end Bridge
end PrimeTensor
