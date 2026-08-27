import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalFubini

/-!
# Second Fourier moment of the actual named selected terminal-tail state

`LocalFubini` identifies the explicit raw Fourier amplitude almost everywhere
with the coercion of the actual named deweighted selected tail `L²` state.

The explicit amplitude already carries the endpoint-quarter second Fourier
moment estimate.  This file transfers that estimate, without any further
measure-theoretic work, to the actual named selected terminal-tail state.

Thus the selected tail itself—not merely an auxiliary pointwise amplitude—has

* an integrable second raw Fourier moment; and
* the same quantitative selected quarter-Hölder second-moment budget.

This is the moment input needed to bootstrap positive-time regularity of the
selected Duhamel state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedTailNamedSecond
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted second-moment density of the actual named deweighted selected
terminal-tail Fourier `L²` state agrees almost everywhere with the already
estimated explicit raw Fourier amplitude density. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 2 *
        ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      ‖ξ‖ ^ 2 *
        ‖h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- The actual named deweighted selected terminal-tail Fourier `L²` state has
an integrable second raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_integrable
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
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hAmplitude :=
    h3SelectedDuhamelTailRawFourierAmplitude_secondMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  exact hAmplitude.congr hEq.symm

/-- Quantitative endpoint-quarter second Fourier-moment budget for the actual
named deweighted selected terminal-tail Fourier `L²` state. -/
theorem integral_secondMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A t := by
  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_secondMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 2 *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 2 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖ := by
    exact integral_congr_ae hEq

  have hBudget :=
    integral_secondMoment_h3SelectedDuhamelTailRawFourierAmplitude_le
      hν U₀ hA hU₀ ht htR i

  exact hIntegralEq.trans_le hBudget

end
end Euclidean
end Bridge
end PrimeTensor
