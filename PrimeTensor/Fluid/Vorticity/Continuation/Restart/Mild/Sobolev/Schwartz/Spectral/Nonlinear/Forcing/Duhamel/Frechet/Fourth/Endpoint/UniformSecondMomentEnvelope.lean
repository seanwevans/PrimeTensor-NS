import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.PositiveTimeCoefficientMonotonicity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.SecondMildMass

/-!
# Uniform positive-time second-moment envelope

The pointwise selected second-moment estimate is already quantitative, but the
full-third bootstrap needs one constant valid for every `r ∈ [a,t]`, with
`0 < a ≤ t`.

Rather than prove the nested pointwise envelope monotone as a whole, we
dominate its pieces independently:

* free heat: evaluate the antitone second-heat coefficient at the lower
  endpoint `a`;
* Duhamel head: evaluate its antitone heat coefficient at `a/2`, but its
  increasing H³ midpoint size at the upper endpoint `t`;
* Duhamel tail old-head length: use `t/2`;
* terminal quarter-Hölder coefficient: enlarge `(r/2,r)` to `(a/2,t)`;
* terminal quarter power: use the upper endpoint `t`;
* frozen second-heat primitive: unchanged.

This gives a slightly coarser but fully explicit scalar envelope valid on the
whole positive interval.  It is exactly the form needed to uniformize the
first forcing moment and then the selected `9/4` state envelope.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzUniformSecondMomentEnvelope
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Uniform terminal-tail second-moment budget on a positive interval `[a,t]`.
The decreasing heat coefficient is frozen at `a/2`; increasing interval
quantities are frozen at `t`. -/
noncomputable def h3SelectedDuhamelTailSecondMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  (t / 2) *
      (h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2))
    +
  12 * ν⁻¹ *
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
        ν A (a / 2) t *
      (t - t / 2) ^ ((1 : ℝ) / 4)
    +
  (((2 * Real.pi) ^ 2 * ν)⁻¹) *
    (4 * h3NonlinearForcingL1Coefficient * A ^ 2)

/-- Uniform selected mild second-moment envelope on `[a,t]`. -/
noncomputable def h3SelectedMildSecondMomentUniformEnvelope
    (ν A a t : ℝ) : ℝ :=
  h3HeatSecondMomentRawL1Coefficient ν a *
      h3RawFourierL1DeweightingCoefficient * A
    +
  h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
      h3RawFourierL1DeweightingCoefficient *
      h3SelectedDuhamelHalfTimeH3Envelope ν A t
    +
  h3SelectedDuhamelTailSecondMomentUniformEnvelope ν A a t

/-- The midpoint H³ Duhamel envelope increases with nonnegative terminal time. -/
theorem h3SelectedDuhamelHalfTimeH3Envelope_mono
    {ν A r t : ℝ}
    (hA : 0 ≤ A)
    (hr : 0 ≤ r)
    (hrt : r ≤ t) :
    h3SelectedDuhamelHalfTimeH3Envelope ν A r
      ≤
    h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
  have hrtHalf : r / 2 ≤ t / 2 := by
    linarith

  have hSqrt :
      Real.sqrt (r / 2) ≤ Real.sqrt (t / 2) :=
    Real.sqrt_le_sqrt hrtHalf

  have hCoeff0 :
      0 ≤
        h3HeatLerayDuhamelPathCoefficient ν *
          (2 * A) * (2 * A) := by
    have hC :
        0 ≤ h3HeatLerayDuhamelPathCoefficient ν :=
      h3HeatLerayDuhamelPathCoefficient_nonneg ν
    positivity

  unfold h3SelectedDuhamelHalfTimeH3Envelope

  calc
    h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt (r / 2) *
          (2 * A) * (2 * A)
        =
      (h3HeatLerayDuhamelPathCoefficient ν *
          (2 * A) * (2 * A)) *
        Real.sqrt (r / 2) := by
      ring
    _ ≤
      (h3HeatLerayDuhamelPathCoefficient ν *
          (2 * A) * (2 * A)) *
        Real.sqrt (t / 2) :=
      mul_le_mul_of_nonneg_left hSqrt hCoeff0
    _ =
      h3HeatLerayDuhamelPathCoefficient ν *
          Real.sqrt (t / 2) *
          (2 * A) * (2 * A) := by
      ring

/-- The canonical selected terminal-tail second-moment budget at any
`r ∈ [a,t]` is dominated by the one explicit interval envelope. -/
theorem h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget ν A r
      ≤
    h3SelectedDuhamelTailSecondMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have ht : 0 < t :=
    lt_of_lt_of_le hr hrt

  have haHalf : 0 < a / 2 := by
    positivity

  have hrHalf : 0 < r / 2 := by
    positivity

  have hHalfOrder : a / 2 ≤ r / 2 := by
    linarith

  have hrtHalf : r / 2 ≤ t / 2 := by
    linarith

  have hC2 :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) :=
    h3HeatSecondMomentRawL1Coefficient_antitone_pos
      hν haHalf hHalfOrder

  have hMass0 :
      0 ≤ 4 * h3NonlinearForcingL1Coefficient * A ^ 2 := by
    have hC : 0 ≤ h3NonlinearForcingL1Coefficient :=
      h3NonlinearForcingL1Coefficient_nonneg
    positivity

  have hHeadCoeff :
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
          ν A r
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
        (4 * h3NonlinearForcingL1Coefficient * A ^ 2) := by
    unfold
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
    exact
      mul_le_mul_of_nonneg_right hC2 hMass0

  have hHeadCoeff0 :
      0 ≤
        h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
          ν A r := by
    unfold
      h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
    exact
      mul_nonneg
        (h3HeatSecondMomentRawL1Coefficient_nonneg ν (r / 2))
        hMass0

  have hHeadUpper0 :
      0 ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2) :=
    mul_nonneg
      (h3HeatSecondMomentRawL1Coefficient_nonneg ν (a / 2))
      hMass0

  have hHeadTerm :
      (r / 2) *
          h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
            ν A r
        ≤
      (t / 2) *
        (h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          (4 * h3NonlinearForcingL1Coefficient * A ^ 2)) := by
    calc
      (r / 2) *
          h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
            ν A r
          ≤
        (t / 2) *
          h3NonlinearForcingQuarterSelectedRestartHalfHeadSecondMomentCoefficient
            ν A r :=
        mul_le_mul_of_nonneg_right hrtHalf hHeadCoeff0
      _ ≤
        (t / 2) *
          (h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
            (4 * h3NonlinearForcingL1Coefficient * A ^ 2)) :=
        mul_le_mul_of_nonneg_left hHeadCoeff (by positivity)

  have hLocal :
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (r / 2) r
        ≤
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2) t :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_halfInterval_le
      hν hA ha har hrt

  have hLocal0 :
      0 ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (r / 2) r :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
      hν.le hA hr.le

  have hLocalUpper0 :
      0 ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2) t :=
    h3NonlinearForcingQuarterSelectedRestartLocalCoefficient_nonneg
      hν.le hA ht.le

  have hLag0 : 0 ≤ r - r / 2 := by
    linarith

  have hLagOrder :
      r - r / 2 ≤ t - t / 2 := by
    linarith

  have hPow :
      (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      (t - t / 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hLag0 hLagOrder (by norm_num)

  have hPow0 :
      0 ≤ (r - r / 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg hLag0 _

  have hPowUpper0 :
      0 ≤ (t - t / 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (by linarith : 0 ≤ t - t / 2) _

  have hLocalPow :
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (r / 2) r *
          (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
          ν A (a / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
    calc
      h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2) r *
            (r - r / 2) ^ ((1 : ℝ) / 4)
          ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t *
            (r - r / 2) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hLocal hPow0
      _ ≤
        h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t *
            (t - t / 2) ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hPow hLocalUpper0

  have hScale0 : 0 ≤ 12 * ν⁻¹ := by
    positivity

  have hVariationTerm :
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2) r *
          (r - r / 2) ^ ((1 : ℝ) / 4)
        ≤
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
    calc
      12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (r / 2) r *
          (r - r / 2) ^ ((1 : ℝ) / 4)
          =
        (12 * ν⁻¹) *
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (r / 2) r *
            (r - r / 2) ^ ((1 : ℝ) / 4)) := by
        ring
      _ ≤
        (12 * ν⁻¹) *
          (h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
              ν A (a / 2) t *
            (t - t / 2) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hLocalPow hScale0
      _ =
        12 * ν⁻¹ *
          h3NonlinearForcingQuarterSelectedRestartLocalCoefficient
            ν A (a / 2) t *
          (t - t / 2) ^ ((1 : ℝ) / 4) := by
        ring

  unfold
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget
    h3NonlinearForcingQuarterSelectedRestartSplitSecondMomentBudget
    h3SelectedDuhamelTailSecondMomentUniformEnvelope

  exact
    add_le_add
      (add_le_add hHeadTerm hVariationTerm)
      (le_refl _)

/-- The original pointwise selected mild second-moment envelope is dominated
by one explicit interval constant on `[a,t]`. -/
theorem h3SelectedMildSecondMomentEnvelope_le_uniform_on
    {ν A a r t : ℝ}
    (hν : 0 < ν)
    (hA : 0 ≤ A)
    (ha : 0 < a)
    (har : a ≤ r)
    (hrt : r ≤ t) :
    h3SelectedMildSecondMomentEnvelope ν A r
      ≤
    h3SelectedMildSecondMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have ht : 0 < t :=
    lt_of_lt_of_le hr hrt

  have hFreeC :
      h3HeatSecondMomentRawL1Coefficient ν r
        ≤
      h3HeatSecondMomentRawL1Coefficient ν a :=
    h3HeatSecondMomentRawL1Coefficient_antitone_pos
      hν ha har

  have hFreeFactor0 :
      0 ≤ h3RawFourierL1DeweightingCoefficient * A :=
    mul_nonneg
      h3RawFourierL1DeweightingCoefficient_nonneg
      hA

  have hFree :
      h3HeatSecondMomentRawL1Coefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A
        ≤
      h3HeatSecondMomentRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
    calc
      h3HeatSecondMomentRawL1Coefficient ν r *
          h3RawFourierL1DeweightingCoefficient * A
          =
        h3HeatSecondMomentRawL1Coefficient ν r *
          (h3RawFourierL1DeweightingCoefficient * A) := by
        ring
      _ ≤
        h3HeatSecondMomentRawL1Coefficient ν a *
          (h3RawFourierL1DeweightingCoefficient * A) :=
        mul_le_mul_of_nonneg_right hFreeC hFreeFactor0
      _ =
        h3HeatSecondMomentRawL1Coefficient ν a *
          h3RawFourierL1DeweightingCoefficient * A := by
        ring

  have haHalf : 0 < a / 2 := by
    positivity

  have hrHalf : 0 < r / 2 := by
    positivity

  have hHalfOrder : a / 2 ≤ r / 2 := by
    linarith

  have hHeadC :
      h3HeatSecondMomentRawL1Coefficient ν (r / 2)
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) :=
    h3HeatSecondMomentRawL1Coefficient_antitone_pos
      hν haHalf hHalfOrder

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

  have hH3t0 :
      0 ≤ h3SelectedDuhamelHalfTimeH3Envelope ν A t :=
    h3SelectedDuhamelHalfTimeH3Envelope_nonneg hA

  have hHead :
      h3SelectedDuhamelHeadSecondMomentEnvelope ν A r
        ≤
      h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
        h3RawFourierL1DeweightingCoefficient *
        h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
    unfold h3SelectedDuhamelHeadSecondMomentEnvelope
    calc
      h3HeatSecondMomentRawL1Coefficient ν (r / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r
          ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A r := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hHeadC hCdw0)
            hH3r0
      _ ≤
        h3HeatSecondMomentRawL1Coefficient ν (a / 2) *
          h3RawFourierL1DeweightingCoefficient *
          h3SelectedDuhamelHalfTimeH3Envelope ν A t := by
        exact
          mul_le_mul_of_nonneg_left
            hH3
            (mul_nonneg
              (h3HeatSecondMomentRawL1Coefficient_nonneg ν (a / 2))
              hCdw0)

  have hTail :=
    h3NonlinearForcingQuarterSelectedRestartSecondMomentBudget_le_uniform_on
      hν hA ha har hrt

  unfold
    h3SelectedMildSecondMomentEnvelope
    h3SelectedDuhamelSecondMomentEnvelope
    h3SelectedMildSecondMomentUniformEnvelope

  simpa only [add_assoc] using
    (add_le_add hFree (add_le_add hHead hTail))

/-- Every selected mild coordinate has its canonical raw Fourier second mass
bounded uniformly on the whole positive interval `[a,t]`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMass_le_uniform_on
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
    h3SpectralScalarRawFourierSecondMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ r i)
      ≤
    h3SelectedMildSecondMomentUniformEnvelope ν A a t := by
  have hr : 0 < r :=
    lt_of_lt_of_le ha har

  have hrR :
      r ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans hrt htR

  have hPoint :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_secondMass_le
      hν U₀ hA hU₀ hr hrR i

  exact
    le_trans hPoint
      (h3SelectedMildSecondMomentEnvelope_le_uniform_on
        hν hA.le ha har hrt)

end
end Euclidean
end Bridge
end PrimeTensor
