import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.LocalFubini

/-!
# Explicit raw Fourier amplitude of the full selected Duhamel contribution

The selected Duhamel state has already been split at the midpoint into:

* a positive-lag head, whose deweighted Fourier `L²` state is represented by
  the explicit heat-evolved raw Fourier amplitude; and
* a terminal-half tail, whose deweighted Fourier `L²` state is represented by
  the explicit source-time-integrated raw Fourier amplitude.

This file simply adds those two explicit representatives and identifies their
sum almost everywhere with the actual deweighted full selected Duhamel state.

No new estimate and no new Fubini argument is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal NNReal Topology Interval Real RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSpectralDuhamelTailSelectedRawFourierAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Explicit raw Fourier amplitude of one coordinate of the complete selected
Duhamel contribution, split into the midpoint head and terminal-half tail. -/
noncomputable def h3SelectedDuhamelRawFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  h3SpectralScalarHeatRawRepresentative
      ν (t / 2)
      (h3SpectralFinHeatLerayDuhamel
        ν (t / 2) hν W W i)
      ξ
    +
  h3SelectedDuhamelTailRawFourierAmplitude
    ν A t hν U₀ hA hU₀ i ξ

/-- The explicit full selected raw Fourier amplitude is an almost-everywhere
representative of the actual named deweighted selected Duhamel coordinate. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_rawAmplitude
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    ((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    h3SelectedDuhamelRawFourierAmplitude
      ν A t hν U₀ hA hU₀ ht i := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  have hFull :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
      hν U₀ hA hU₀ ht i

  have hHead :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
      hν U₀ hA hU₀ ht i

  have hTail :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2_ae_eq_rawAmplitude
      hν U₀ hA hU₀ ht i

  filter_upwards [hFull, hHead, hTail] with ξ hFullξ hHeadξ hTailξ

  unfold h3SelectedDuhamelRawFourierAmplitude
  dsimp only [W]
  rw [hFullξ, hHeadξ, hTailξ]

end

end Euclidean
end Bridge
end PrimeTensor
