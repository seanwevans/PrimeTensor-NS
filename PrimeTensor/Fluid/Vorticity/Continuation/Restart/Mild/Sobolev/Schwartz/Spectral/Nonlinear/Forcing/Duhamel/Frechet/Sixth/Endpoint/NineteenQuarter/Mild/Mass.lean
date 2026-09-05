import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Sixth.Endpoint.NineteenQuarter.Duhamel.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Mild.Mass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarter.Duhamel.Head.Mass

/-!
# Sixth Fréchet endpoint: selected nineteen-quarter mild mass

The complete selected Duhamel contribution now has a quantitative `19/4`
raw Fourier moment. To close the same moment on the selected mild state, only
the positive-time free heat contribution remains.

Split the positive heat time into two equal pieces,

    H_t = H_{t/2} H_{t/2},

and split the radial weight as

    19/4 = 4 + 3/4.

The first heat half supplies the already-compiled full-fourth multiplier, while
the second supplies the residual `3/4` multiplier. Hence

    |ξ|^(19/4) |H_t(ξ)|
      ≤
    C₄(ν,t/2) C_{3/4}(ν,t/2).

This file packages that free-heat estimate, transfers it to the named
quotient-safe free-heat Fourier state, recombines

    selected mild = free heat + selected Duhamel,

and finally transfers the quantitative `19/4` bound to the canonical
pointwise raw Fourier representative consumed by the next nonlinear layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzSixthEndpointNineteenQuarterMildMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Positive-time free-heat `19/4` multiplier coefficient obtained from a
half-time fourth-moment factor and a half-time residual `3/4` factor. -/
noncomputable def h3HeatNineteenQuarterRawL1Coefficient
    (ν t : ℝ) : ℝ :=
  h3HeatFourthRawL1Coefficient ν (t / 2) *
    h3HeatThreeQuarterMomentCoefficient ν (t / 2)

theorem h3HeatNineteenQuarterRawL1Coefficient_nonneg
    {ν t : ℝ}
    (hν : 0 ≤ ν)
    (ht : 0 ≤ t) :
    0 ≤ h3HeatNineteenQuarterRawL1Coefficient ν t := by
  unfold h3HeatNineteenQuarterRawL1Coefficient
  exact
    mul_nonneg
      (h3HeatFourthRawL1Coefficient_nonneg
        hν (by positivity))
      (h3HeatThreeQuarterMomentCoefficient_nonneg
        hν (by positivity))

/-- Pointwise positive-time `19/4` heat multiplier bound. -/
theorem norm_h3HeatFourierSymbol_nineteenQuarter_le
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (ξ : H3FourierPoint3) :
    h3FourierNineteenQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν t ξ‖
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν t := by
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

  have hFourth :=
    norm_h3HeatFourierSymbol_fourth_le
      hν hhalf ξ

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

  have hFourthCoeff0 :
      0 ≤
        h3HeatFourthRawL1Coefficient ν (t / 2) :=
    h3HeatFourthRawL1Coefficient_nonneg
      hν.le hhalf.le

  unfold h3HeatNineteenQuarterRawL1Coefficient

  rw [
    h3FourierNineteenQuarterWeight_eq_fourth_mul_threeQuarter,
    hSplit
  ]

  calc
    (‖ξ‖ ^ 4 * h3FourierThreeQuarterWeight ξ) *
        (‖h3HeatFourierSymbol ν (t / 2) ξ‖ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖)
        =
      (‖ξ‖ ^ 4 *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) *
        (h3FourierThreeQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ‖) := by
      ring
    _ ≤
      h3HeatFourthRawL1Coefficient ν (t / 2) *
        h3HeatThreeQuarterMomentCoefficient ν (t / 2) :=
      mul_le_mul
        hFourth
        hThreeQuarter
        hThreeQuarterLhs0
        hFourthCoeff0

/-- The explicit positive-time free heat representative has an integrable
`19/4` raw Fourier moment. -/
theorem h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatNineteenQuarterRawL1Coefficient ν t

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
      Continuous h3FourierNineteenQuarterWeight := by
    unfold h3FourierNineteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (19 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      (h3SpectralScalarHeatRawRepresentative_aestronglyMeasurable
        ν t G).norm

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_nineteenQuarter_le
      hν ht ξ

  have hTargetNonneg :
      0 ≤
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖ := by
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  have hBound :
      h3FourierNineteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
        ≤
      C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    calc
      h3FourierNineteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        h3HeatNineteenQuarterRawL1Coefficient ν t *
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

/-- Quantitative positive-time free-heat `19/4` raw Fourier mass from the input
raw `L¹` mass. -/
theorem h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integral_le_rawL1
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν t *
      h3SpectralScalarRawFourierL1Mass G := by
  let C : ℝ :=
    h3HeatNineteenQuarterRawL1Coefficient ν t

  have hTarget :=
    h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integrable
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
        h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖
          ≤
        C * ‖h3SpectralScalarRawFourier G ξ‖ := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_nineteenQuarter_le
        hν ht ξ

    unfold h3SpectralScalarHeatRawRepresentative
    rw [norm_mul]

    calc
      h3FourierNineteenQuarterWeight ξ *
          (‖h3HeatFourierSymbol ν t ξ‖ *
            ‖h3SpectralScalarRawFourier G ξ‖)
          =
        (h3FourierNineteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν t ξ‖) *
          ‖h3SpectralScalarRawFourier G ξ‖ := by
        ring
      _ ≤
        h3HeatNineteenQuarterRawL1Coefficient ν t *
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
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatNineteenQuarterRawL1Coefficient ν t *
          ‖h3SpectralScalarRawFourier G ξ‖ :=
      hIntegral
    _ =
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        ∫ ξ : H3FourierPoint3,
          ‖h3SpectralScalarRawFourier G ξ‖ := by
      rw [integral_const_mul]

/-- Quantitative free-heat `19/4` smoothing directly from the H³ solver norm. -/
theorem h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integral_le_norm
    {ν t : ℝ}
    (hν : 0 < ν)
    (ht : 0 < t)
    (G : H3SpectralScalarState) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      ‖G‖ := by
  have hBase :=
    h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integral_le_rawL1
      hν ht G

  have hRaw :=
    h3SpectralScalarRawFourierL1Mass_le_norm G

  have hCoeff0 :
      0 ≤ h3HeatNineteenQuarterRawL1Coefficient ν t :=
    h3HeatNineteenQuarterRawL1Coefficient_nonneg
      hν.le ht.le

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative ν t G ξ‖)
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        h3SpectralScalarRawFourierL1Mass G :=
      hBase
    _ ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        (h3RawFourierL1DeweightingCoefficient * ‖G‖) :=
      mul_le_mul_of_nonneg_left
        hRaw hCoeff0
    _ =
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖G‖ := by
      ring

/-- The selected initial free-heat coordinate has an explicit `19/4` moment
bound in terms of the restart radius parameter `A`. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeat_nineteenQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (_hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integral_le_norm
      hν ht (U₀ i)

  have hCoord :
      ‖U₀ i‖ ≤ A :=
    le_trans
      (h3SpectralVelocity_coordinate_norm_le U₀ i)
      hU₀

  have hCoeff0 :
      0 ≤
        h3HeatNineteenQuarterRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient :=
    mul_nonneg
      (h3HeatNineteenQuarterRawL1Coefficient_nonneg
        hν.le ht.le)
      h3RawFourierL1DeweightingCoefficient_nonneg

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖)
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        ‖U₀ i‖ :=
      hHeat
    _ ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A :=
      mul_le_mul_of_nonneg_left
        hCoord hCoeff0

/-- The named free positive-time heat term has an integrable `19/4` raw Fourier
moment. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integrable
    {ν t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (ht : 0 < t)
    (i : Fin 3) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hHeat :=
    h3SpectralScalarHeatRawRepresentative_nineteenQuarterMoment_integrable
      hν ht (U₀ i)

  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hWeighted :
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  exact hHeat.congr hWeighted.symm

/-- Quantitative free-heat `19/4` bound on the named quotient-safe raw Fourier
`L²` state. -/
theorem h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integral_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
              hν U₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatNineteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A := by
  have hRep :=
    h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_ae_eq_heatRepresentative
      hν U₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2
                hν U₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖h3SpectralScalarHeatRawRepresentative
            ν t (U₀ i) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  rw [hIntegralEq]

  exact
    h3SpectralFinHeatLeraySelectedInitialHeat_nineteenQuarterMoment_integral_le
      hν U₀ hA hU₀ ht i

/-- Pointwise positive-time `19/4` moment envelope for one selected mild
coordinate. -/
noncomputable def h3SelectedMildNineteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatNineteenQuarterRawL1Coefficient ν t *
      h3RawFourierL1DeweightingCoefficient *
      A
    +
  h3SelectedDuhamelNineteenQuarterMomentEnvelope ν A t

/-- Every positive-time coordinate of the named selected mild raw Fourier `L²`
state has an integrable `19/4` moment throughout the restart interval. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integrable
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
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamel :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeat.add hDuhamel

  have hWeightContinuous :
      Continuous h3FourierNineteenQuarterWeight := by
    unfold h3FourierNineteenQuarterWeight
    exact
      continuous_norm.rpow_const
        (fun _ =>
          Or.inr
            (by norm_num : 0 ≤ (19 : ℝ) / 4))

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
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
      0 ≤ h3FourierNineteenQuarterWeight ξ := by
    unfold h3FourierNineteenQuarterWeight
    exact Real.rpow_nonneg (norm_nonneg ξ) _

  have hTargetNonneg :
      0 ≤ h3FourierNineteenQuarterWeight ξ * ‖W ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  rw [hξ]

  calc
    h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖
        ≤
      h3FourierNineteenQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_sub_le (H ξ) (D ξ))
        hw
    _ =
      h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
        h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
      ring

/-- Every positive-time coordinate of the named selected mild raw Fourier `L²`
state has the quantitative `19/4` moment bound. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integral_le
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
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedMildNineteenQuarterMomentEnvelope ν A t := by
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
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ ht i

  have hDuhamelInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integrable
        hν U₀ hA hU₀ ht htR i

  have hFullInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integrable
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
        h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFullInt.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
            h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHeatInt.add hDuhamelInt

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierNineteenQuarterWeight ξ := by
      unfold h3FourierNineteenQuarterWeight
      exact Real.rpow_nonneg (norm_nonneg ξ) _

    calc
      h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖
          ≤
        h3FourierNineteenQuarterWeight ξ * (‖H ξ‖ + ‖D ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (H ξ) (D ξ))
          hw
      _ =
        h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hHeatBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖)
        ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
        h3RawFourierL1DeweightingCoefficient *
        A := by
    dsimp only [H]
    exact
      h3SpectralFinHeatLeraySelectedInitialHeatRawFourierL2_nineteenQuarterMoment_integral_le
        hν U₀ hA hU₀ ht i

  have hDuhamelBound :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖)
        ≤
      h3SelectedDuhamelNineteenQuarterMomentEnvelope ν A t := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_nineteenQuarterMoment_integral_le
        hν U₀ hA hU₀ ht htR i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
    integral_congr_ae hWeightedRep

  unfold h3SelectedMildNineteenQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖W ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ * ‖H ξ - D ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierNineteenQuarterWeight ξ * ‖H ξ‖ +
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖H ξ‖) +
        ∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ * ‖D ξ‖ := by
      rw [integral_add hHeatInt hDuhamelInt]
    _ ≤
      h3HeatNineteenQuarterRawL1Coefficient ν t *
          h3RawFourierL1DeweightingCoefficient *
          A
        +
      h3SelectedDuhamelNineteenQuarterMomentEnvelope ν A t :=
      add_le_add hHeatBound hDuhamelBound

/-- Raw Fourier `19/4` mass of a scalar spectral H³ state. -/
noncomputable def h3SpectralScalarRawFourierNineteenQuarterMass
    (F : H3SpectralScalarState) : ℝ :=
  ∫ ξ : H3FourierPoint3,
    h3FourierNineteenQuarterWeight ξ *
      ‖h3SpectralScalarRawFourier F ξ‖

/-- The weighted `19/4` density of the canonical raw Fourier representative
agrees almost everywhere with the named selected mild raw Fourier `L²`
package. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineteenQuarterMoment_ae_eq_rawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3) :
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineteenQuarterWeight ξ *
        ‖h3SpectralScalarRawFourier
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ t i) ξ‖)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3FourierNineteenQuarterWeight ξ *
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
coordinate has an integrable `19/4` moment. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMoment_integrable
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
          ‖h3SpectralScalarRawFourier
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ t i) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integrable
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineteenQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  exact hNamed.congr hEq.symm

/-- The canonical raw Fourier representative of one selected positive-time
coordinate has the same quantitative `19/4` moment bound. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_rawFourier_nineteenQuarterMass_le
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3) :
    h3SpectralScalarRawFourierNineteenQuarterMass
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ t i)
      ≤
    h3SelectedMildNineteenQuarterMomentEnvelope ν A t := by
  have hNamed :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2_nineteenQuarterMoment_integral_le
      hν U₀ hA hU₀ ht htR i

  have hEq :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_nineteenQuarterMoment_ae_eq_rawFourierL2
      (t := t)
      hν U₀ hA hU₀ i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierNineteenQuarterWeight ξ *
            ‖h3SpectralScalarRawFourier
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                hν U₀ hA hU₀ t i) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierNineteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayMildSolutionAtRestartRadiusRawFourierL2
              hν U₀ hA hU₀ t i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖ :=
    integral_congr_ae hEq

  unfold h3SpectralScalarRawFourierNineteenQuarterMass
  rw [hIntegralEq]
  exact hNamed

/-- Raw Fourier `19/4` mass is nonnegative. -/
theorem h3SpectralScalarRawFourierNineteenQuarterMass_nonneg
    (F : H3SpectralScalarState) :
    0 ≤ h3SpectralScalarRawFourierNineteenQuarterMass F := by
  unfold h3SpectralScalarRawFourierNineteenQuarterMass
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
