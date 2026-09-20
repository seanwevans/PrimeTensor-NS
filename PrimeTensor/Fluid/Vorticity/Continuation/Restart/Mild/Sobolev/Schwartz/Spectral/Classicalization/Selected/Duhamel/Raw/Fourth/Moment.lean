import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Duhamel.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Selected.C1.Representative

/-!
# Classicalization: fourth moment of the named selected Duhamel raw amplitude

The higher endpoint branch already proves the full fourth raw Fourier moment of
the selected Duhamel `L²` representative:

    ∫ |ξ|⁴ |D_raw,L²(t,ξ)| dξ < ∞.

The pointwise Duhamel reconstruction stack also proves that this `L²`
representative agrees almost everywhere with the explicit named amplitude

    h3SelectedDuhamelRawFourierAmplitude.

This file transports the fourth moment across that a.e. identification.

The resulting theorem is stated for the named raw amplitude because the
order-two old-history heat quotient multiplies the scalar heat quotient by two
fixed coordinate symbols; together with the heat generator this costs exactly
four Fourier powers.

No new estimate or Fourier interchange is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedDuhamelRawFourthMoment
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The explicit named selected Duhamel raw Fourier amplitude has an
integrable fourth radial moment at every strict positive time inside the
restart radius. -/
theorem h3SelectedDuhamelRawFourierAmplitude_fourthMoment_integrable
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
        ‖ξ‖ ^ 4 *
          ‖h3SelectedDuhamelRawFourierAmplitude
            ν A t hν U₀ hA hU₀ ht i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hL2 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 4 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
                (t := t) hν U₀ hA hU₀ i :
              H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3) :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fourthMoment_integrable
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
