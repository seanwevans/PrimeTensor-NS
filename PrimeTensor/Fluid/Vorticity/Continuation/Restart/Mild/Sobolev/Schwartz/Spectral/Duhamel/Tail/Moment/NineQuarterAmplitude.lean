import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.NineQuarterFullFubini

/-!
# Selected terminal-tail nine-quarter Fourier amplitude

The full selected terminal-half `9/4` Duhamel kernel is now genuinely
integrable on source-time × frequency.

This file pushes that product-space result through the same amplitude layer
already used for the integer second moment.

For one velocity coordinate define

    T_{9/4,i}(ξ)
      =
    ∫_{t/2}^t
      |ξ|^(9/4) H_{t-s}(ξ) N_i(W(s), W(s))(ξ) ds.

Fubini gives `T_{9/4,i} ∈ L¹_ξ`.  Since the Fourier weight is independent of
source time, linearity of the Bochner integral gives

    T_{9/4,i}(ξ)
      =
    |ξ|^(9/4) T_i(ξ),

where `T_i` is the already-defined raw selected terminal-tail amplitude.

Consequently the raw selected tail has an integrable `9/4` Fourier moment.

No new endpoint estimate is introduced here.  This is the amplitude packaging
of the product integrability closed in `NineQuarterFullFubini`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSelectedNineQuarterAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Source-time integral of the full selected complex `9/4` weighted kernel. -/
noncomputable def h3SelectedDuhamelTailNineQuarterFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelTailNineQuarterComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- The full selected `9/4` Fourier amplitude is genuinely `L¹` in
frequency. -/
theorem h3SelectedDuhamelTailNineQuarterFourierAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailNineQuarterFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelTailNineQuarterComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailNineQuarterFourierAmplitude
  exact hOuter

/-- Pulling the `9/4` frequency weight through the source-time integral
identifies the weighted amplitude with the weight times the raw selected tail
amplitude. -/
theorem h3SelectedDuhamelTailNineQuarterFourierAmplitude_eq_weight_mul_raw
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailNineQuarterFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ
      =
    (h3FourierNineQuarterWeight ξ : ℂ) *
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  unfold
    h3SelectedDuhamelTailNineQuarterFourierAmplitude
    h3SelectedDuhamelTailNineQuarterComplexKernel
    h3SelectedDuhamelTailRawFourierAmplitude

  change
    (∫ s in Set.Ioo (t / 2) t,
      (h3FourierNineQuarterWeight ξ : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    (h3FourierNineQuarterWeight ξ : ℂ) *
      ∫ s in Set.Ioo (t / 2) t,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)

  rw [integral_const_mul]

/-- The actual raw selected terminal-tail amplitude has an integrable
`9/4` Fourier moment. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_nineQuarterMoment_integrable
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
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hWeighted :=
    h3SelectedDuhamelTailNineQuarterFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hNorm := hWeighted.norm

  refine hNorm.congr ?_
  filter_upwards with ξ

  have hWeight0 :
      0 ≤ h3FourierNineQuarterWeight ξ := by
    unfold h3FourierNineQuarterWeight
    positivity

  rw [
    h3SelectedDuhamelTailNineQuarterFourierAmplitude_eq_weight_mul_raw
      hν U₀ hA hU₀ i ξ,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0
  ]

end
end Euclidean
end Bridge
end PrimeTensor
