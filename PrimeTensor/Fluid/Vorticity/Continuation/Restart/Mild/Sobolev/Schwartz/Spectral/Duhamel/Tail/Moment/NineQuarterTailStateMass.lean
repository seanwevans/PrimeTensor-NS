import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullNineQuarter

/-!
# Quantitative nine-quarter mass of the named selected terminal-tail state

`NineQuarterTailMass` gives the numerical `9/4` raw Fourier mass bound for the
explicit selected terminal-tail amplitude.

`FullNineQuarter` already proves that the weighted density of the named
quotient-safe terminal-tail `L²` state agrees almost everywhere with that
explicit raw amplitude density.

This file transfers the numerical estimate across that a.e. representative
identity:

    ∫ |ξ|^(9/4) |T_named(ξ)| dξ
      ≤
    h3SelectedDuhamelTailNineQuarterBudget ν A t.

No new analytic estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzNineQuarterTailStateMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The named quotient-safe selected terminal-tail `L²` state inherits the
explicit quantitative `9/4` raw Fourier mass bound. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelTailNineQuarterBudget ν A t := by
  have hEq :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_nineQuarterMoment_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖ :=
    integral_congr_ae hEq

  rw [hIntegralEq]

  exact
    h3SelectedDuhamelTailRawFourierAmplitude_nineQuarterMass_le
      hν U₀ hA hU₀ ht htR i

end
end Euclidean
end Bridge
end PrimeTensor
