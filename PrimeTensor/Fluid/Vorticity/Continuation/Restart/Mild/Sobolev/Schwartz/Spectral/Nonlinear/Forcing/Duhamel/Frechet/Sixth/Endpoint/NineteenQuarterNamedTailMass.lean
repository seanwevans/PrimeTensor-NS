import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarterTailAmplitude
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NamedSecond

/-!
# Sixth Fréchet endpoint: named selected nineteen-quarter terminal-tail mass

`NineteenQuarterTailAmplitude` proves that the explicit selected terminal-tail
raw Fourier amplitude has an integrable and quantitatively bounded `19/4`
moment.

The actual midpoint Duhamel decomposition uses the quotient-safe named
deweighted terminal-tail `L²` state. `NamedSecond` supplies the a.e.
representative identity

    named tail raw Fourier = explicit raw tail amplitude.

This file multiplies that identity by the radial `19/4` weight and transfers
both integrability and the quantitative budget to the exact named tail state
used by the selected Duhamel decomposition.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNamedNineteenQuarterTail
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted `19/4` density of the actual named deweighted selected
terminal-tail Fourier `L²` state agrees almost everywhere with the explicitly
estimated raw terminal-tail amplitude density. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineteenQuarterMoment_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineteenQuarterWeight ξ *
        ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
            (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineteenQuarterWeight ξ *
        ‖h3SelectedDuhamelTailRawFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- The actual named selected terminal-tail Fourier `L²` state has an
integrable `19/4` raw Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineteenQuarterMoment_integrable
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
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hAmplitude :=
    h3SelectedDuhamelTailRawFourierAmplitude_nineteenQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineteenQuarterMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  exact hAmplitude.congr hEq.symm

/-- Quantitative `19/4` Fourier-moment budget for the actual named selected
terminal-tail Fourier `L²` state. -/
theorem integral_nineteenQuarterMoment_h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelNineteenQuarterUniformBudget
      ν A (t / 2) t := by
  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineteenQuarterMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖ := by
    exact integral_congr_ae hEq

  have hBudget :=
    integral_nineteenQuarterMoment_h3SelectedDuhamelTailRawFourierAmplitude_le
      hν U₀ hA hU₀ ht htR i

  exact hIntegralEq.trans_le hBudget

end
end Euclidean
end Bridge
end PrimeTensor
