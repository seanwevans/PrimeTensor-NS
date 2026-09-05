import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SevenQuarterMajorant

/-!
# Full-third terminal variation: frequency sections

The selected unheated nonlinear forcing now has an integrable `5/4` raw
Fourier moment at every positive restart time.

For two positive source times `s < t`, the weighted forcing difference

    |ξ|^(5/4) |N(W(s),W(s))(ξ) - N(W(t),W(t))(ξ)|

is therefore integrable by the triangle inequality.

`SevenQuarterHeat` supplies the complementary residual heat weight

    3 = 5/4 + 7/4,

with terminal lag coefficient proportional to `(t-s)^(-7/8)`.

This file combines those two facts at one strict source time.  It proves that
every frequency section of the selected terminal variation kernel at a full
third Fourier moment is genuinely integrable.

No source-time uniformity is asserted here.  That quantitative issue remains
isolated for the later Fubini checkpoint.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzThirdVariationSection
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A positive heat lag sends a Fourier-L¹ amplitude carrying an integrable
`5/4` moment to a complex amplitude with an integrable full third moment. -/
theorem h3HeatFourierSymbol_third_weighted_mul_integrable_of_fiveQuarter
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F (volume : Measure H3FourierPoint3))
    (hF5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
          (h3HeatFourierSymbol ν τ ξ * F ξ))
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ := h3HeatSevenQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatSevenQuarterMomentCoefficient_nonneg
        hν.le hτ.le

  have hWeightComplexContinuous :
      Continuous
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_norm.pow 3)

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          ((‖ξ‖ ^ 3 : ℝ) : ℂ) *
            (h3HeatFourierSymbol ν τ ξ * F ξ))
        (volume : Measure H3FourierPoint3) :=
    hWeightComplexContinuous.aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        hF.aestronglyMeasurable)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C *
            (h3FourierFiveQuarterWeight ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF5.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_sevenQuarter_le
      hν hτ ξ

  have hFive0 :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  rw [
    norm_mul,
    Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg ξ) 3),
    norm_mul,
    h3FourierNorm_cubed_eq_fiveQuarter_mul_sevenQuarter
  ]

  calc
    (h3FourierFiveQuarterWeight ξ *
        h3FourierSevenQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
        =
      h3FourierFiveQuarterWeight ξ *
        (h3FourierSevenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ‖) *
        ‖F ξ‖ := by
      ring
    _ ≤
      h3FourierFiveQuarterWeight ξ * C * ‖F ξ‖ := by
      have hScaled :
          h3FourierFiveQuarterWeight ξ *
              (h3FourierSevenQuarterWeight ξ *
                ‖h3HeatFourierSymbol ν τ ξ‖)
            ≤
          h3FourierFiveQuarterWeight ξ * C :=
        mul_le_mul_of_nonneg_left hHeat hFive0
      exact
        mul_le_mul_of_nonneg_right hScaled (norm_nonneg (F ξ))
    _ =
      C *
        (h3FourierFiveQuarterWeight ξ * ‖F ξ‖) := by
      ring

/-- The difference of two amplitudes with integrable `5/4` moments again has
an integrable `5/4` moment. -/
theorem h3FourierFiveQuarterWeight_mul_norm_sub_integrable
    (F G : H3FourierPoint3 → ℂ)
    (hF :
      Integrable F (volume : Measure H3FourierPoint3))
    (hG :
      Integrable G (volume : Measure H3FourierPoint3))
    (hF5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3))
    (hG5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖G ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ‖ +
            h3FourierFiveQuarterWeight ξ * ‖G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hF5.add hG5

  have hWeightContinuous :
      Continuous h3FourierFiveQuarterWeight := by
    unfold h3FourierFiveQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ => Or.inr (by norm_num : 0 ≤ (5 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (hF.sub hG).aestronglyMeasurable.norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hw :
      0 ≤ h3FourierFiveQuarterWeight ξ := by
    unfold h3FourierFiveQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTarget0 :
      0 ≤
        h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0
  ]

  calc
    h3FourierFiveQuarterWeight ξ * ‖F ξ - G ξ‖
        ≤
      h3FourierFiveQuarterWeight ξ * (‖F ξ‖ + ‖G ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (F ξ) (G ξ))
        hw
    _ =
      h3FourierFiveQuarterWeight ξ * ‖F ξ‖ +
        h3FourierFiveQuarterWeight ξ * ‖G ξ‖ := by
      ring

/-- Selected terminal variation kernel with a full third Fourier weight. -/
noncomputable def h3SelectedDuhamelTailThirdVariationComplexKernel
    (ν A t : ℝ)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (p : ℝ × H3FourierPoint3) : ℂ :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀
  ((‖p.2‖ ^ 3 : ℝ) : ℂ) *
    (h3HeatFourierSymbol ν (t - p.1) p.2 *
      (h3RawFinLerayOuterProductDivergence
          (W p.1) (W p.1) i p.2 -
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i p.2))

/-- At every strict source time in a positive terminal interval, the selected
full-third variation kernel is integrable in frequency. -/
theorem h3SelectedDuhamelTailThirdVariationComplexKernel_section_integrable
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3SelectedDuhamelTailThirdVariationComplexKernel
          ν A t hν U₀ hA hU₀ i (s, ξ))
      (volume : Measure H3FourierPoint3) := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let Ns : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W s) (W s) i

  let Nt : H3FourierPoint3 → ℂ :=
    h3RawFinLerayOuterProductDivergence
      (W t) (W t) i

  let D : H3FourierPoint3 → ℂ :=
    fun ξ => Ns ξ - Nt ξ

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have ht0 : 0 < t :=
    lt_trans ha hat

  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hNs :
      Integrable Ns (volume : Measure H3FourierPoint3) := by
    dsimp only [Ns]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W s) (W s) i

  have hNt :
      Integrable Nt (volume : Measure H3FourierPoint3) := by
    dsimp only [Nt]
    exact
      h3RawFinLerayOuterProductDivergence_integrable
        (W t) (W t) i

  have hNs5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖Ns ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Ns, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hNt5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖Nt ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [Nt, W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ ht0 htR i

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hNs.sub hNt

  have hD5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3FourierFiveQuarterWeight_mul_norm_sub_integrable
        Ns Nt hNs hNt hNs5 hNt5

  have hτ : 0 < t - s :=
    sub_pos.mpr hs.2

  have hWeighted :=
    h3HeatFourierSymbol_third_weighted_mul_integrable_of_fiveQuarter
      hν hτ D hD hD5

  simpa only [
    h3SelectedDuhamelTailThirdVariationComplexKernel,
    D, Ns, Nt, W
  ] using hWeighted

/-- Quantitative one-section estimate: the full-third frequency integral is
controlled by the normalized `7/4` heat coefficient times the `5/4` weighted
mass of the forcing difference. -/
theorem h3SelectedDuhamelTailThirdVariation_frequencyIntegral_le
    {ν A a t s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (hat : a < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (hs : s ∈ Set.Ioo a t)
    (i : Fin 3) :
    let W : ℝ → H3SpectralFinVectorState :=
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
        hν U₀ hA hU₀
    let D : H3FourierPoint3 → ℂ :=
      fun ξ =>
        h3RawFinLerayOuterProductDivergence
            (W s) (W s) i ξ -
          h3RawFinLerayOuterProductDivergence
            (W t) (W t) i ξ
    (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 *
          ‖h3HeatFourierSymbol ν (t - s) ξ * D ξ‖)
      ≤
    h3HeatSevenQuarterTerminalMajorant ν t s *
      (∫ ξ : H3FourierPoint3,
        h3FourierFiveQuarterWeight ξ * ‖D ξ‖) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let D : H3FourierPoint3 → ℂ :=
    fun ξ =>
      h3RawFinLerayOuterProductDivergence
          (W s) (W s) i ξ -
        h3RawFinLerayOuterProductDivergence
          (W t) (W t) i ξ

  have hs0 : 0 < s :=
    lt_trans ha hs.1

  have ht0 : 0 < t :=
    lt_trans ha hat

  have hsR : s ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hs.2.le htR

  have hFs :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W s) (W s) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W s) (W s) i

  have hFt :
      Integrable
        (h3RawFinLerayOuterProductDivergence
          (W t) (W t) i)
        (volume : Measure H3FourierPoint3) :=
    h3RawFinLerayOuterProductDivergence_integrable
      (W t) (W t) i

  have hD :
      Integrable D (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hFs.sub hFt

  have hFs5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W s) (W s) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ hs0 hsR i

  have hFt5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ *
            ‖h3RawFinLerayOuterProductDivergence
              (W t) (W t) i ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3RawFinLerayOuterProductDivergence_selectedRestart_fiveQuarterMoment_integrable
        hν U₀ hA hU₀ ht0 htR i

  have hD5 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFiveQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3FourierFiveQuarterWeight_mul_norm_sub_integrable
        (h3RawFinLerayOuterProductDivergence
          (W s) (W s) i)
        (h3RawFinLerayOuterProductDivergence
          (W t) (W t) i)
        hFs hFt hFs5 hFt5

  have hτ : 0 < t - s :=
    sub_pos.mpr hs.2

  have hBound :=
    h3HeatFourierSymbol_third_norm_integral_le_of_fiveQuarter
      hν hτ D hD hD5

  rw [
    h3HeatSevenQuarterMomentCoefficient_sub_eq_terminalMajorant
      hν hs.2
  ] at hBound

  exact hBound

end
end Euclidean
end Bridge
end PrimeTensor
