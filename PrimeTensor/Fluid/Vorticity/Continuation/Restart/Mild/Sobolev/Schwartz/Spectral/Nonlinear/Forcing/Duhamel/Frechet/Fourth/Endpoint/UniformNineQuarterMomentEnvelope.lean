import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.UniformQuarterForcingEnvelope
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.MildNineQuarterMass

/-!
# Uniform positive-time nine-quarter state envelope

The selected pointwise `9/4` state estimate is now fully quantitative.  The
full-third variation bootstrap, however, needs one scalar `M₉` valid for every
time `r` in a fixed positive interval `[a,t]`.

The pointwise envelope has four time-dependent pieces:

* free heat: `C₉/₄(ν,r) C_dw A`;
* Duhamel midpoint head:
  `C₉/₄(ν,r/2) C_dw B_H³(r)`;
* terminal variation:
  `8 C_var(ν,K(r/2,r)) (r-r/2)^(1/8)`;
* terminal frozen term:
  `c_ν B_{1/4}(ν,A,r)`.

The previous checkpoints provide exactly the required interval comparisons:

* `C₉/₄` is antitone in positive heat time;
* the midpoint H³ envelope is monotone in terminal time;
* `K(r/2,r) ≤ K(a/2,t)`;
* the selected quarter forcing mass is uniformly bounded on `[a,t]`.

This file packages those facts into one explicit interval constant
`h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t` and proves that every
selected coordinate satisfies the corresponding `9/4` raw Fourier mass bound
throughout `[a,t]`.

No new PDE or Fourier estimate is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzUniformNineQuarterMomentEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform `9/4` variation-tail budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailNineQuarterVariationUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  8 *
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
      ν
      (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (a / 2) t) *
    (t - t / 2) ^ ((1 : ℝ) / 8)

/-- Uniform `9/4` frozen-tail budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailNineQuarterFrozenUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    h3SelectedForcingQuarterMomentUniformEnvelope ν A a t

/-- Uniform complete terminal-tail `9/4` budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelTailNineQuarterUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelTailNineQuarterVariationUniformEnvelope ν A a t +
    h3SelectedDuhamelTailNineQuarterFrozenUniformEnvelope ν A a t

/-- Uniform midpoint-head `9/4` budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelHeadNineQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatNineQuarterMomentCoefficient ν (a / 2) *
    h3RawFourierL1DeweightingCoefficient *
    h3SelectedDuhamelHalfTimeH3Envelope ν A t

/-- Uniform complete selected Duhamel `9/4` budget on `[a,t]`. -/
noncomputable def h3SelectedDuhamelNineQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3SelectedDuhamelHeadNineQuarterMomentUniformEnvelope ν A a t +
    h3SelectedDuhamelTailNineQuarterUniformEnvelope ν A a t

/-- Uniform selected mild-state `9/4` budget on `[a,t]`. -/
noncomputable def h3SelectedMildNineQuarterMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatNineQuarterMomentCoefficient ν a *
      h3RawFourierL1DeweightingCoefficient * A
    +
  h3SelectedDuhamelNineQuarterMomentUniformEnvelope ν A a t

/-- The normalized `9/4` cancellation coefficient is monotone in its
nonnegative quarter-Hölder constant. -/
theorem h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient_mono
    {ν K₁ K₂ : ℝ}
    (hν : 0 < ν)
    (hK : K₁ ≤ K₂) :
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν K₁
      ≤
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν K₂ := by
  unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
  exact
    mul_le_mul_of_nonneg_left
      hK
      (Real.rpow_nonneg (by positivity : 0 ≤ 3 * ν⁻¹) _)

/-- The pointwise selected `9/4` variation-tail budget is dominated by the
interval-uniform variation budget. -/
theorem h3SelectedDuhamelTailNineQuarterVariationBudget_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelTailNineQuarterVariationBudget ν A r
      ≤
    h3SelectedDuhamelTailNineQuarterVariationUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have ht : 0 < t :=
    lt_of_lt_of_le hr hrt

  let Kr : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (r / 2) r

  let Ku : ℝ :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
      ν A (a / 2) t

  let Cr : ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν Kr

  let Cu : ℝ :=
    h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient ν Ku

  have hK : Kr ≤ Ku := by
    dsimp only [Kr, Ku]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_halfInterval_le
        hν hA ha har hrt

  have hKr0 : 0 ≤ Kr := by
    dsimp only [Kr]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
        hν.le hA hr.le

  have hKu0 : 0 ≤ Ku := by
    dsimp only [Ku]
    exact
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
        hν.le hA ht.le

  have hC : Cr ≤ Cu := by
    dsimp only [Cr, Cu]
    exact
      h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient_mono
        hν hK

  have hBase0 : 0 ≤ (3 * ν⁻¹) ^ ((9 : ℝ) / 8) :=
    Real.rpow_nonneg (by positivity) _

  have hCr0 : 0 ≤ Cr := by
    dsimp only [Cr]
    unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
    exact mul_nonneg hBase0 hKr0

  have hCu0 : 0 ≤ Cu := by
    dsimp only [Cu]
    unfold h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
    exact mul_nonneg hBase0 hKu0

  have hLag0 : 0 ≤ r - r / 2 := by
    linarith

  have hLagUpper0 : 0 ≤ t - t / 2 := by
    linarith

  have hLag :
      r - r / 2 ≤ t - t / 2 := by
    linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      (t - t / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow hLag0 hLag (by norm_num)

  have hPow0 :
      0 ≤ (r - r / 2) ^ ((1 : ℝ) / 8) :=
    Real.rpow_nonneg hLag0 _

  have hEightC :
      8 * Cr ≤ 8 * Cu :=
    mul_le_mul_of_nonneg_left hC (by norm_num)

  have hEightCu0 : 0 ≤ 8 * Cu :=
    mul_nonneg (by norm_num) hCu0

  unfold
    h3SelectedDuhamelTailNineQuarterVariationBudget
    h3SelectedDuhamelTailNineQuarterVariationUniformEnvelope

  dsimp only [Kr, Ku, Cr, Cu]

  calc
    8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2) r) *
        (r - r / 2) ^ ((1 : ℝ) / 8)
        ≤
      8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t) *
        (r - r / 2) ^ ((1 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right hEightC hPow0
    _ ≤
      8 *
        h3NonlinearForcingHeatNineQuarterQuarterCancellationCoefficient
          ν
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t) *
        (t - t / 2) ^ ((1 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hPow hEightCu0

/-- The pointwise selected frozen `9/4` tail budget is dominated by the
interval-uniform frozen budget. -/
theorem h3SelectedDuhamelTailNineQuarterFrozenBudget_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelTailNineQuarterFrozenBudget ν A r
      ≤
    h3SelectedDuhamelTailNineQuarterFrozenUniformEnvelope ν A a t := by
  have hQuarter :=
    h3SelectedForcingQuarterMomentEnvelope_le_uniform_on
      hν hA ha har hrt

  have hc0 :
      0 ≤ (((2 * Real.pi) ^ 2 * ν)⁻¹) := by
    positivity

  unfold
    h3SelectedDuhamelTailNineQuarterFrozenBudget
    h3SelectedDuhamelTailNineQuarterFrozenUniformEnvelope

  exact
    mul_le_mul_of_nonneg_left hQuarter hc0

/-- The complete pointwise selected terminal-tail `9/4` budget is dominated
by the interval-uniform tail budget. -/
theorem h3SelectedDuhamelTailNineQuarterBudget_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelTailNineQuarterBudget ν A r
      ≤
    h3SelectedDuhamelTailNineQuarterUniformEnvelope ν A a t := by
  unfold
    h3SelectedDuhamelTailNineQuarterBudget
    h3SelectedDuhamelTailNineQuarterUniformEnvelope

  exact
    add_le_add
      (h3SelectedDuhamelTailNineQuarterVariationBudget_le_uniform_on
        hν hA ha har hrt)
      (h3SelectedDuhamelTailNineQuarterFrozenBudget_le_uniform_on
        hν hA ha har hrt)

/-- The pointwise midpoint-head `9/4` budget is dominated by the
interval-uniform head budget. -/
theorem h3SelectedDuhamelHeadNineQuarterMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelHeadNineQuarterMomentEnvelope ν A r
      ≤
    h3SelectedDuhamelHeadNineQuarterMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have haHalf : 0 < a / 2 := by
    positivity

  have hHalf :
      a / 2 ≤ r / 2 := by
    linarith

  have hHeat :
      h3HeatNineQuarterMomentCoefficient ν (r / 2)
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2) :=
    h3HeatNineQuarterMomentCoefficient_antitone_pos
      hν haHalf hHalf

  have hH3 :
      h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
    h3SelectedDuhamelHalfTimeH3Envelope_mono
      hA hr.le hrt

  have hCdw0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient :=
    h3RawFourierL1DeweightingCoefficient_nonneg

  have hH3r0 :
      0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A r :=
    h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA

  have hHeatUpper0 :
      0 ≤ h3HeatNineQuarterMomentCoefficient ν (a / 2) :=
    h3HeatNineQuarterMomentCoefficient_nonneg
      hν.le (by positivity)

  unfold
    h3SelectedDuhamelHeadNineQuarterMomentEnvelope
    h3SelectedDuhamelHeadNineQuarterMomentUniformEnvelope

  calc
    h3HeatNineQuarterMomentCoefficient ν (r / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r
        ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r := by
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hHeat hCdw0)
          hH3r0
    _ ≤
      h3HeatNineQuarterMomentCoefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
      exact
        mul_le_mul_of_nonneg_left
          hH3
          (mul_nonneg hHeatUpper0 hCdw0)

/-- The complete pointwise selected Duhamel `9/4` envelope is dominated by one
interval-uniform Duhamel envelope. -/
theorem h3SelectedDuhamelNineQuarterMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelNineQuarterMomentEnvelope ν A r
      ≤
    h3SelectedDuhamelNineQuarterMomentUniformEnvelope ν A a t := by
  unfold
    h3SelectedDuhamelNineQuarterMomentEnvelope
    h3SelectedDuhamelNineQuarterMomentUniformEnvelope

  exact
    add_le_add
      (h3SelectedDuhamelHeadNineQuarterMomentEnvelope_le_uniform_on
        hν hA ha har hrt)
      (h3SelectedDuhamelTailNineQuarterBudget_le_uniform_on
        hν hA ha har hrt)

/-- The complete pointwise selected mild-state `9/4` envelope is dominated by
one interval-uniform state envelope. -/
theorem h3SelectedMildNineQuarterMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedMildNineQuarterMomentEnvelope ν A r
      ≤
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t := by
  have hHeat :
      h3HeatNineQuarterMomentCoefficient ν r
        ≤
      h3HeatNineQuarterMomentCoefficient ν a :=
    h3HeatNineQuarterMomentCoefficient_antitone_pos
      hν ha har

  have hFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg
      h3RawFourierL1DeweightingCoefficient_nonneg
      hA

  have hFree :
      h3HeatNineQuarterMomentCoefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A
        ≤
      h3HeatNineQuarterMomentCoefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
    calc
      h3HeatNineQuarterMomentCoefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A
          =
        h3HeatNineQuarterMomentCoefficient ν r *
          (h3RawFourierL1DeweightingCoefficient * A) := by
        ring
      _ ≤
        h3HeatNineQuarterMomentCoefficient ν a *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right hHeat hFactor0
      _ =
        h3HeatNineQuarterMomentCoefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
        ring

  have hDuhamel :=
    h3SelectedDuhamelNineQuarterMomentEnvelope_le_uniform_on
      hν hA ha har hrt

  unfold
    h3SelectedMildNineQuarterMomentEnvelope
    h3SelectedMildNineQuarterMomentUniformEnvelope

  exact
    add_le_add hFree hDuhamel

/-- Every selected mild coordinate has one canonical raw Fourier `9/4` mass
bound valid throughout the positive interval `[a,t]`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineQuarterWeight ξ *
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ r i) ξ‖)
      ≤
    h3SelectedMildNineQuarterMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hPoint :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineQuarterMass_le
      hν U₀ hA hU₀ hr hrR i

  exact
    le_trans hPoint
      (h3SelectedMildNineQuarterMomentEnvelope_le_uniform_on
        hν hA.le ha har hrt)

end
end Euclidean
end Bridge
end PrimeTensor
