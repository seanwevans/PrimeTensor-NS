import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdFullTailMass

/-!
# Quantitative full-third selected terminal-tail amplitude

`ThirdFullTailMass` closes the actual selected radial-third terminal-half kernel
on source-time × frequency:

    |ξ|³ H_{t-s}(ξ) N(W(s),W(s))(ξ),

with an explicit iterated norm budget.

This file pushes that product-space result through the already-defined raw
selected terminal-tail Fourier amplitude

    T_i(ξ)
      =
    ∫_{(t/2,t)}
      H_{t-s}(ξ) N_i(W(s),W(s))(ξ) ds.

Because the radial weight is independent of source time,

    ∫ |ξ|³ H_{t-s} N_s ds
      =
    |ξ|³ T_i(ξ).

Thus the actual raw terminal-tail amplitude has an integrable third Fourier
moment, quantitatively bounded by the complete full-third terminal-tail budget.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdTailAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Source-time integral of the selected radial-third weighted terminal-tail
kernel. -/
noncomputable def h3SelectedDuhamelTailThirdFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelTailThirdComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- The selected radial-third weighted terminal-tail Fourier amplitude is
genuinely `L¹` in frequency. -/
theorem h3SelectedDuhamelTailThirdFourierAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailThirdFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hProd :=
    h3SelectedDuhamelTailThirdComplexKernel_fubini_integrable
      hν U₀ hA hU₀ ht htR i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailThirdFourierAmplitude
  exact hOuter

/-- Pulling the radial third Fourier weight through the source-time integral
identifies the weighted amplitude with `|ξ|³` times the actual raw selected
terminal-tail amplitude. -/
theorem h3SelectedDuhamelTailThirdFourierAmplitude_eq_weight_mul_raw
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailThirdFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ
      =
    ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  unfold
    h3SelectedDuhamelTailThirdFourierAmplitude
    h3SelectedDuhamelTailThirdComplexKernel
    h3SelectedDuhamelTailRawFourierAmplitude

  change
    (∫ s in Set.Ioo (t / 2) t,
      ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
      ∫ s in Set.Ioo (t / 2) t,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)

  rw [integral_const_mul]

/-- The actual raw selected terminal-tail amplitude has an integrable third
Fourier moment. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_thirdMoment_integrable
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
        ‖ξ‖ ^ 3 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hWeighted :=
    h3SelectedDuhamelTailThirdFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hNorm := hWeighted.norm

  refine hNorm.congr ?_
  filter_upwards with ξ

  have hPow0 : 0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  rw [
    h3SelectedDuhamelTailThirdFourierAmplitude_eq_weight_mul_raw
      hν U₀ hA hU₀ i ξ,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hPow0
  ]

/-- Quantitative third Fourier-moment budget for the actual raw selected
terminal-tail amplitude. -/
theorem integral_thirdMoment_h3SelectedDuhamelTailRawFourierAmplitude_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    h3SelectedDuhamelTailThirdFullBudget ν A t := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelTailThirdComplexKernel
      ν A t hν U₀ hA hU₀ i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ∫ s : ℝ,
        ‖Z (s, ξ)‖
        ∂μt

  have hProd :
      Integrable
        Z
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailThirdComplexKernel_fubini_integrable
        hν U₀ hA hU₀ ht htR i

  have hMInt :
      Integrable
        M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M]
    exact hProd.integral_norm_prod_right

  have hWeightedInt :=
    h3SelectedDuhamelTailThirdFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hWeightedNormInt := hWeightedInt.norm

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailThirdFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖
          ≤
        M ξ := by
    intro ξ
    calc
      ‖h3SelectedDuhamelTailThirdFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖
          =
        ‖∫ s : ℝ,
            Z (s, ξ)
            ∂μt‖ := by
          rfl
      _ ≤
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
          ∂μt :=
        norm_integral_le_integral_norm _
      _ =
        M ξ := by
          rfl

  have hWeightedOuterLe :
      (∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailThirdFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3, M ξ := by
    exact
      integral_mono
        hWeightedNormInt
        hMInt
        hPointwise

  have hSwap :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        =
      ∫ ξ : H3FourierPoint3,
        ∫ s : ℝ,
          ‖Z (s, ξ)‖
        ∂μt := by
    exact
      MeasureTheory.integral_integral_swap
        (f := fun s : ℝ => fun ξ : H3FourierPoint3 => ‖Z (s, ξ)‖)
        hProd.norm

  have hBudget :
      (∫ s : ℝ,
          ∫ ξ : H3FourierPoint3,
            ‖Z (s, ξ)‖
          ∂(volume : Measure H3FourierPoint3)
        ∂μt)
        ≤
      h3SelectedDuhamelTailThirdFullBudget ν A t := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelTailThirdComplexKernel_iteratedNormIntegral_le
        hν U₀ hA hU₀ ht htR i

  calc
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailThirdFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      have hPow0 : 0 ≤ ‖ξ‖ ^ 3 :=
        pow_nonneg (norm_nonneg ξ) 3
      rw [
        h3SelectedDuhamelTailThirdFourierAmplitude_eq_weight_mul_raw
          hν U₀ hA hU₀ i ξ,
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hPow0
      ]
    _ ≤
      ∫ ξ : H3FourierPoint3, M ξ :=
      hWeightedOuterLe
    _ =
      ∫ s : ℝ,
        ∫ ξ : H3FourierPoint3,
          ‖Z (s, ξ)‖
        ∂(volume : Measure H3FourierPoint3)
      ∂μt :=
      hSwap.symm
    _ ≤
      h3SelectedDuhamelTailThirdFullBudget ν A t :=
      hBudget

end
end Euclidean
end Bridge
end PrimeTensor
