import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterDuhamelMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdMildMass

/-!
# Fifth Fréchet endpoint: selected fifteen-quarter mild mass

The complete selected Duhamel contribution now has a quantitative `15/4`
raw Fourier moment.  To close the same moment on the selected mild state we
only need the positive-time free heat contribution.

The existing heat multiplier infrastructure is quantitative through integer
moment three.  We obtain `15/4` by splitting the positive heat time into two
equal pieces:

    H_t = H_{t/2} H_{t/2},

and splitting the radial weight as

    15/4 = 3 + 3/4.

The first heat half supplies the already-compiled cubic multiplier, while the
second supplies the residual `3/4` multiplier from
`FifteenQuarterDuhamelHeadMass`.  Hence

    |ξ|^(15/4) |H_t(ξ)|
      ≤
    C₃(ν,t/2) C_{3/4}(ν,t/2).

This file packages that free-heat estimate, transfers it to the named
quotient-safe free-heat Fourier state, then recombines

    selected mild = free heat + selected Duhamel

at the raw Fourier `L²` level.  Finally the bound is transferred to the
canonical pointwise raw Fourier representative consumed by the nonlinear
forcing layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterMildMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-time free-heat `15/4` multiplier coefficient obtained from a
half-time cubic factor and a half-time residual `3/4` factor. -/
noncomputable def h3HeatFifteenQuarterRawL1Coefficient
    (ν t : ℝ) : ℝ :=
  h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
    h3HeatThreeQuarterMomentCoefficient ν (t / 2)

theorem h3HeatFifteenQuarterRawL1Coefficient_nonneg
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t) :
    0 ≤ h3HeatFifteenQuarterRawL1Coefficient ν t := by
  unfold h3HeatFifteenQuarterRawL1Coefficient
  exact
    mul_nonneg
      (h3HeatThirdMomentRawL1Coefficient_nonneg ν (t / 2))
      (h3HeatThreeQuarterMomentCoefficient_nonneg
        hν (by positivity))

/-- Pointwise positive-time `15/4` heat multiplier bound. -/
theorem norm_h3HeatFourierSymbol_fifteenQuarter_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (ξ : H3FourierPoint3) :
    h3FourierFifteenQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν t ξ‖
      ≤
    h3HeatFifteenQuarterRawL1Coefficient ν t := by
  have hhalf : 0 < t / 2 := by
    positivity

  have hSplit :
      ‖h3HeatFourierSymbol ν t ξ‖
        =
      ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
        ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
    have htSplit :
        (t / 2) + (t / 2) = t := by
      ring
    calc
      ‖h3HeatFourierSymbol ν t ξ‖
          =
        ‖h3HeatFourierSymbol ν ((t / 2) + (t / 2)) ξ‖ := by
          rw [htSplit]
      _ =
        ‖h3HeatFourierSymbol ν (t / 2) ξ *
          h3HeatFourierSymbol ν (t / 2) ξ‖ := by
          rw [h3HeatFourierSymbol_add]
      _ =
        ‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
          rw [norm_mul]

  have hThird0 :
      ‖ξ‖ ^ 3 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖
        ≤
      h3HeatThirdMomentRawL1Coefficient ν (t / 2) := by
    have h :=
      h3HeatFourierMomentMultiplier_le_three
        hν hhalf 3 (by norm_num) ξ
    simpa [h3HeatThirdMomentRawL1Coefficient] using h

  have hThreeQuarter :=
    norm_h3HeatFourierSymbol_threeQuarter_le
      hν hhalf ξ

  have hThreeQuarterLhs0 :
      0 ≤
        h3FourierThreeQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖ := by
    unfold h3FourierThreeQuarterWeight
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  have hThirdCoeff0 :
      0 ≤
        h3HeatThirdMomentRawL1Coefficient ν (t / 2) :=
    h3HeatThirdMomentRawL1Coefficient_nonneg _ _

  unfold h3HeatFifteenQuarterRawL1Coefficient

  rw [
    h3FourierFifteenQuarterWeight_eq_cubed_mul_threeQuarter,
    hSplit
  ]

  calc
    (‖ξ‖ ^ 3 * h3FourierThreeQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖)
        =
      (‖ξ‖ ^ 3 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) *
        (h3FourierThreeQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) := by
      ring
    _ ≤
      h3HeatThirdMomentRawL1Coefficient ν (t / 2) *
        h3HeatThreeQuarterMomentCoefficient ν (t / 2) := by
      exact
        mul_le_mul
          hThird0
          hThreeQuarter
          hThreeQuarterLhs0
          hThirdCoeff0

/-- The explicit positive-time free heat representative has an integrable
`15/4` raw Fourier moment. -/
theorem h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatFifteenQuarterRawL1Coefficient ν t

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.const_mul C

  have hWeightContinuous :
      Continuous h3FourierFifteenQuarterWeight := by
    unfold h3FourierFifteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (15 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G).norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_fifteenQuarter_le
      hν ht ξ

  have hTargetNonneg :
      0 ≤
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ := by
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  have hBound :
      h3FourierFifteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
        ≤
      C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    calc
      h3FourierFifteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        h3HeatFifteenQuarterRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          hHeat
          (norm_nonneg _)
      _ =
        C * ‖h3SpectralScalarRawFourier G ξ‖ := by
        rfl

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  simpa only [
    h3SpectralScalarHeatRawRepresentative,
    norm_mul
  ] using hBound

/-- Quantitative positive-time free-heat `15/4` raw Fourier mass from the input
raw `L¹` mass. -/
theorem h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integral_le_rawL1
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatFifteenQuarterRawL1Coefficient ν t *
      h3SpectralScalarRawFourierL1Mass G := by
  let C : ℝ :=
    h3HeatFifteenQuarterRawL1Coefficient ν t

  have hTarget :=
    h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integrable
      hν ht G

  have hRaw :
      Integrable
        (h3SpectralScalarRawFourier G)
        (volume : Measure H3FourierPoint3) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (h3SpectralScalarRawFourier_memLp1 G)

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * ‖h3SpectralScalarRawFourier G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hRaw.norm.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
          ≤
        C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_fifteenQuarter_le
        hν ht ξ

    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]

    calc
      h3FourierFifteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        h3HeatFifteenQuarterRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
        mul_le_mul_of_nonneg_right
          hHeat
          (norm_nonneg _)
      _ =
        C * ‖h3SpectralScalarRawFourier G ξ‖ := by
        rfl

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  dsimp only [C] at hIntegral ⊢
  unfold h3SpectralScalarRawFourierL1Mass

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatFifteenQuarterRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
      hIntegral
    _ =
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      rw [integral_const_mul]

/-- Quantitative free-heat `15/4` smoothing directly from the H³ solver norm. -/
theorem h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integral_le_norm
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatFifteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      ‖G‖ := by
  have hBase :=
    h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integral_le_rawL1
      hν ht G

  have hRaw :=
    h3SpectralScalarRawFourierL1Mass_le_norm G

  have hCoeff0 :
      0 ≤ h3HeatFifteenQuarterRawL1Coefficient ν t :=
    h3HeatFifteenQuarterRawL1Coefficient_nonneg
      hν.le ht.le

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        h3SpectralScalarRawFourierL1Mass G :=
      hBase
    _ ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        (h3RawFourierL1DeweightingCoefficient * ‖G‖) :=
      mul_le_mul_of_nonneg_left
        hRaw hCoeff0
    _ =
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ := by
      ring

/-- The selected initial free-heat coordinate has an explicit `15/4` moment
bound in terms of the restart radius parameter `A`. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeat_fifteenQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (_hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
      ≤
    h3HeatFifteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integral_le_norm
      hν ht (U₀ i)

  have hCoord :
      ‖U₀ i‖ ≤ A :=
    le_trans
      (h3SpectralVelocity_coordinate_norm_le U₀ i)
      hU₀

  have hCoeff0 :
      0 ≤
        h3HeatFifteenQuarterRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      (h3HeatFifteenQuarterRawL1Coefficient_nonneg
        hν.le ht.le)
      h3RawFourierL1DeweightingCoefficient_nonneg

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
        ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖U₀ i‖ :=
      hHeat
    _ ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A :=
      mul_le_mul_of_nonneg_left
        hCoord hCoeff0

/-- The named free positive-time heat term has an integrable `15/4` raw Fourier
moment. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_fifteenQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_fifteenQuarterMoment_integrable
      hν ht (U₀ i)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeighted.symm

/-- Quantitative free-heat `15/4` bound on the named quotient-safe raw Fourier
`L²` state. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_fifteenQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatFifteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  exact
    h3SpectralFinHeatLeraySelectedInitialHeat_fifteenQuarterMoment_integral_le
      hν U₀ hA hU₀ ht i

/-- Pointwise positive-time `15/4` moment envelope for one selected mild
coordinate. -/
noncomputable def h3SelectedMildFifteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatFifteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A
    +
  h3SelectedDuhamelFifteenQuarterMomentEnvelope ν A t

/-- Every positive-time coordinate of the named selected mild raw Fourier `L²`
state has an integrable `15/4` moment throughout the restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_fifteenQuarterMoment_integrable
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
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeat :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_fifteenQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierFifteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat.add hDuhamel

  have hWeightContinuous :
      Continuous h3FourierFifteenQuarterWeight := by
    unfold h3FourierFifteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (15 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable W).norm

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards [hRep] with ξ hξ

  have hw :
      0 ≤ h3FourierFifteenQuarterWeight ξ := by
    unfold h3FourierFifteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤ h3FourierFifteenQuarterWeight ξ * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖
        ≤
      h3FourierFifteenQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (H ξ) (D ξ))
        hw
    _ =
      h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
        h3FourierFifteenQuarterWeight ξ * ‖D ξ‖ := by
      ring

/-- The named quotient-safe raw Fourier `L²` state of one selected mild
coordinate has `15/4` moment bounded by the sum of the explicit free-heat and
full-Duhamel budgets. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_fifteenQuarterMoment_integral_le
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
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildFifteenQuarterMomentEnvelope ν A t := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
      hν U₀ ht i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let W : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
      hν U₀ hA hU₀ t i

  have hHeatInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_fifteenQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_fifteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hRep :
      ((W : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ - D ξ) := by
    dsimp only [W, H, D]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_heat_add_duhamel
        hν U₀ hA hU₀ ht htR i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierFifteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierFifteenQuarterWeight ξ := by
      unfold h3FourierFifteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierFifteenQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (H ξ) (D ξ))
          hw
      _ =
        h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_fifteenQuarterMoment_integral_le
        hν U₀ hA hU₀ ht i

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖)
        ≤
      h3SelectedDuhamelFifteenQuarterMomentEnvelope ν A t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_fifteenQuarterMoment_integral_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildFifteenQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierFifteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatFifteenQuarterRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient *
          A
        +
      h3SelectedDuhamelFifteenQuarterMomentEnvelope ν A t :=
      add_le_add hHeatBound hDuhamelBound

/-- Raw Fourier `15/4` mass of a scalar spectral H³ state. -/
noncomputable def h3SpectralScalarRawFourierFifteenQuarterMass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierFifteenQuarterWeight ξ *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- The weighted `15/4` density of the canonical raw Fourier representative
agrees almost everywhere with the named selected mild raw Fourier `L²`
package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fifteenQuarterMoment_ae_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierFifteenQuarterWeight ξ *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierFifteenQuarterWeight ξ *
        ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
            hν U₀ hA hU₀ t i : H3FourierComplexL2) :
          H3FourierPoint3 → ℂ) ξ‖) := by
  have hRep :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_ae_eq_rawFourier
      (t := t)
      hν U₀ hA hU₀ i

  filter_upwards [hRep] with ξ hξ
  rw [← hξ]

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has an integrable `15/4` moment. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMoment_integrable
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
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_fifteenQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fifteenQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  exact hNamed.congr hEq.symm

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has the same quantitative `15/4` moment bound. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_fifteenQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierFifteenQuarterMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ t i)
      ≤
    h3SelectedMildFifteenQuarterMomentEnvelope ν A t := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_fifteenQuarterMoment_integral_le
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_fifteenQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierFifteenQuarterMass
  rw [hIntegralEq]
  exact hNamed

/-- Raw Fourier `15/4` mass is nonnegative. -/
theorem h3SpectralScalarRawFourierFifteenQuarterMass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierFifteenQuarterMass F := by
  unfold h3SpectralScalarRawFourierFifteenQuarterMass
  exact
    integral_nonneg fun ξ => by
      exact
        mul_nonneg
          (Real.rpow_nonneg (norm_nonneg ξ) _)
          (norm_nonneg _)

end
end Euclidean
end Bridge
end PrimeTensor
