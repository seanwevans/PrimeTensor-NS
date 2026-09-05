import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Uniform.Second.Forcing.Envelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.Amplitude

/-!
# Fifth Fréchet endpoint: selected fifteen-quarter terminal-tail amplitude

`UniformSecondForcingEnvelope` closes the actual selected `15/4` source kernel
on every positive source interval.  On the terminal half `(t/2,t)` this gives

    ∬ |ξ|^(15/4) |H_{t-s}(ξ) N_s(ξ)| dξ ds
      ≤
    h3SelectedDuhamelFifteenQuarterUniformBudget ν A (t/2) t.

This file pushes that product-space estimate through the already-defined raw
selected terminal-tail Fourier amplitude

    T_i(ξ)
      =
    ∫_{(t/2,t)}
      H_{t-s}(ξ) N_i(W(s),W(s))(ξ) ds.

Because the radial weight is independent of source time,

    ∫ |ξ|^(15/4) H_{t-s} N_s ds
      =
    |ξ|^(15/4) T_i(ξ).

Thus the actual raw terminal-tail amplitude has an integrable and
quantitatively bounded `15/4` Fourier moment.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterTailAmplitude
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Source-time integral of the selected radial-`15/4` weighted terminal-tail
kernel. -/
noncomputable def h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) : ℂ :=
  ∫ s in Set.Ioo (t / 2) t,
    h3SelectedDuhamelFifteenQuarterComplexKernel
      ν A t hν U₀ hA hU₀ i (s, ξ)

/-- The selected radial-`15/4` weighted terminal-tail Fourier amplitude is
genuinely `L¹` in frequency. -/
theorem h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_integrable
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    Integrable
      (h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
        ν A t hν U₀ hA hU₀ i)
      (volume : Measure H3FourierPoint3) := by
  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalf : t / 2 < t := by
    linarith

  have hProd :=
    h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_uniformEnvelope
      hν U₀ hA hU₀ hhalf0 hhalf htR i

  have hOuter := hProd.integral_prod_right

  unfold h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
  exact hOuter

/-- Pulling the radial `15/4` Fourier weight through the source-time integral
identifies the weighted amplitude with the weight times the actual raw
selected terminal-tail amplitude. -/
theorem h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_eq_weight_mul_raw
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (ξ : H3FourierPoint3) :
    h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ
      =
    ((h3FourierFifteenQuarterWeight ξ : ℝ) : ℂ) *
      h3SelectedDuhamelTailRawFourierAmplitude
        ν A t hν U₀ hA hU₀ i ξ := by
  unfold
    h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
    h3SelectedDuhamelFifteenQuarterComplexKernel
    h3SelectedDuhamelTailRawFourierAmplitude

  change
    (∫ s in Set.Ioo (t / 2) t,
      ((h3FourierFifteenQuarterWeight ξ : ℝ) : ℂ) *
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      =
    ((h3FourierFifteenQuarterWeight ξ : ℝ) : ℂ) *
      ∫ s in Set.Ioo (t / 2) t,
        h3SelectedDuhamelTailComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ)

  rw [integral_const_mul]

/-- The actual raw selected terminal-tail amplitude has an integrable
`15/4` Fourier moment. -/
theorem h3SelectedDuhamelTailRawFourierAmplitude_fifteenQuarterMoment_integrable
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
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hWeighted :=
    h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hNorm := hWeighted.norm

  refine hNorm.congr ?_
  filter_upwards with ξ

  have hWeight0 :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  rw [
    h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_eq_weight_mul_raw
      hν U₀ hA hU₀ i ξ,
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg hWeight0
  ]

/-- Quantitative `15/4` Fourier-moment budget for the actual raw selected
terminal-tail amplitude. -/
theorem integral_fifteenQuarterMoment_h3SelectedDuhamelTailRawFourierAmplitude_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
      ≤
    h3SelectedDuhamelFifteenQuarterUniformBudget
      ν A (t / 2) t := by
  let μt : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (t / 2) t)

  let Z : ℝ × H3FourierPoint3 → ℂ :=
    h3SelectedDuhamelFifteenQuarterComplexKernel
      ν A t hν U₀ hA hU₀ i

  let M : H3FourierPoint3 → ℝ :=
    fun ξ =>
      ∫ s : ℝ,
        ‖Z (s, ξ)‖
        ∂μt

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalf : t / 2 < t := by
    linarith

  have hProd :
      Integrable
        Z
        (μt.prod (volume : Measure H3FourierPoint3)) := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_fubini_integrable_uniformEnvelope
        hν U₀ hA hU₀ hhalf0 hhalf htR i

  have hMInt :
      Integrable
        M
        (volume : Measure H3FourierPoint3) := by
    dsimp only [M]
    exact hProd.integral_norm_prod_right

  have hWeightedInt :=
    h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_integrable
      hν U₀ hA hU₀ ht htR i

  have hWeightedNormInt := hWeightedInt.norm

  have hPointwise :
      ∀ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖
          ≤
        M ξ := by
    intro ξ
    calc
      ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
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
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
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
      h3SelectedDuhamelFifteenQuarterUniformBudget
        ν A (t / 2) t := by
    dsimp only [Z, μt]
    exact
      h3SelectedDuhamelFifteenQuarterComplexKernel_iteratedNormIntegral_le_uniformEnvelope
        hν U₀ hA hU₀ hhalf0 hhalf htR i

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SelectedDuhamelTailRawFourierAmplitude
            ν A t hν U₀ hA hU₀ i ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        ‖h3SelectedDuhamelTailFifteenQuarterFourierAmplitude
          ν A t hν U₀ hA hU₀ i ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      have hWeight0 :
          0 ≤ h3FourierFifteenQuarterWeight ξ := by
        unfold h3FourierFifteenQuarterWeight
        exact Real.rpow_nonneg (norm_nonneg ξ) _
      rw [
        h3SelectedDuhamelTailFifteenQuarterFourierAmplitude_eq_weight_mul_raw
          hν U₀ hA hU₀ i ξ,
        norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg hWeight0
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
      h3SelectedDuhamelFifteenQuarterUniformBudget
        ν A (t / 2) t :=
      hBudget

end
end Euclidean
end Bridge
end PrimeTensor
