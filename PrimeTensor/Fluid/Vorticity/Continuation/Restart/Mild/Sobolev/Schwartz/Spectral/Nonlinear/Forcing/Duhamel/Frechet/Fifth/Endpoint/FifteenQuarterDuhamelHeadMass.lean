import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.FifteenQuarterNamedTailMass
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fourth.Endpoint.ThirdDuhamelMass

/-!
# Fifth Fréchet endpoint: quantitative fifteen-quarter Duhamel midpoint head

The selected terminal tail now has a quantitative `15/4` raw Fourier moment.
The midpoint head is the shorter-time selected Duhamel state evolved through
the strictly positive heat lag `t/2`.

The half-time Duhamel state already has a quantitative cubic raw Fourier
moment.  Therefore only the residual heat weight

    15/4 - 3 = 3/4

is needed.

The `3/4` heat multiplier is obtained by interpolating the heat zeroth and
first moment bounds:

    |ξ|^(3/4) |H_τ(ξ)|
      ≤
    C_{3/4}(ν,τ),

with lag singularity `τ^(-3/8)`.

Thus

    m_{15/4}(H_{t/2} D(t/2))
      ≤
    C_{3/4}(ν,t/2) m₃(D(t/2)).

The final statements transfer this estimate to the quotient-safe named
selected midpoint-head Fourier `L²` state.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFifthEndpointFifteenQuarterDuhamelHeadMass
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Residual heat weight after a cubic source moment is inserted into the
`15/4` endpoint. -/
noncomputable def h3FourierThreeQuarterWeight
    (ξ : H3FourierPoint3) : ℝ :=
  ‖ξ‖ ^ ((3 : ℝ) / 4)

/-- The `3/4` radial weight is the `3/4` real power of the first integer
weight. -/
theorem h3FourierThreeQuarterWeight_eq_one_rpow
    (ξ : H3FourierPoint3) :
    h3FourierThreeQuarterWeight ξ
      =
    (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) := by
  have hr : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold h3FourierThreeQuarterWeight

  calc
    ‖ξ‖ ^ ((3 : ℝ) / 4)
        =
      ‖ξ‖ ^ ((1 : ℝ) * ((3 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      (‖ξ‖ ^ (1 : ℝ)) ^ ((3 : ℝ) / 4) := by
        rw [Real.rpow_mul hr]
    _ =
      (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) := by
        rw [Real.rpow_one, pow_one]

/-- Positive-lag heat coefficient for the residual `3/4` Fourier weight. -/
noncomputable def h3HeatThreeQuarterMomentCoefficient
    (ν τ : ℝ) : ℝ :=
  (((Real.sqrt (ν * (τ / 3)))⁻¹) ^ 1) ^ ((3 : ℝ) / 4)

theorem h3HeatThreeQuarterMomentCoefficient_nonneg
    {ν τ : ℝ}
    (_hν : 0 ≤ ν)
    (_hτ : 0 ≤ τ) :
    0 ≤ h3HeatThreeQuarterMomentCoefficient ν τ := by
  unfold h3HeatThreeQuarterMomentCoefficient
  positivity

/-- Pointwise `3/4` heat smoothing by interpolation between the zeroth and
first integer heat moment bounds. -/
theorem norm_h3HeatFourierSymbol_threeQuarter_le
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (ξ : H3FourierPoint3) :
    h3FourierThreeQuarterWeight ξ *
        ‖h3HeatFourierSymbol ν τ ξ‖
      ≤
    h3HeatThreeQuarterMomentCoefficient ν τ := by
  let H : ℝ :=
    ‖h3HeatFourierSymbol ν τ ξ‖

  let C : ℝ :=
    (Real.sqrt (ν * (τ / 3)))⁻¹

  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact norm_nonneg _

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity

  have hH1 : H ≤ 1 := by
    dsimp only [H]
    exact
      norm_h3HeatFourierSymbol_le_one
        hν.le hτ.le ξ

  have h1 :
      ‖ξ‖ ^ 1 * H
        ≤
      C ^ 1 := by
    dsimp only [H, C]
    exact
      h3HeatFourierMomentMultiplier_le_three
        hν hτ 1 (by norm_num) ξ

  have hProd0 :
      0 ≤ ‖ξ‖ ^ 1 * H := by
    positivity

  have hFirst :
      (‖ξ‖ ^ 1 * H) ^ ((3 : ℝ) / 4)
        ≤
      (C ^ 1) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow
      hProd0 h1 (by norm_num)

  have hRemain :
      H ^ ((1 : ℝ) / 4) ≤ 1 := by
    have h :=
      Real.rpow_le_rpow
        hH0 hH1 (by norm_num : 0 ≤ (1 : ℝ) / 4)
    simpa using h

  have hHsplit :
      H ^ ((3 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)
        =
      H := by
    rw [
      ← Real.rpow_add_of_nonneg
        hH0
        (by norm_num : 0 ≤ (3 : ℝ) / 4)
        (by norm_num : 0 ≤ (1 : ℝ) / 4)
    ]
    norm_num

  calc
    h3FourierThreeQuarterWeight ξ * H
        =
      (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) * H := by
        rw [h3FourierThreeQuarterWeight_eq_one_rpow]
    _ =
      (‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
        (H ^ ((3 : ℝ) / 4) *
          H ^ ((1 : ℝ) / 4)) := by
        rw [hHsplit]
    _ =
      ((‖ξ‖ ^ 1) ^ ((3 : ℝ) / 4) *
          H ^ ((3 : ℝ) / 4)) *
        H ^ ((1 : ℝ) / 4) := by
        ring
    _ =
      (‖ξ‖ ^ 1 * H) ^ ((3 : ℝ) / 4) *
        H ^ ((1 : ℝ) / 4) := by
        rw [
          ← Real.mul_rpow
            (pow_nonneg (norm_nonneg ξ) 1)
            hH0
        ]
    _ ≤
      (C ^ 1) ^ ((3 : ℝ) / 4) * 1 := by
        exact
          mul_le_mul
            hFirst hRemain
            (Real.rpow_nonneg hH0 _)
            (Real.rpow_nonneg (pow_nonneg hC0 1) _)
    _ =
      h3HeatThreeQuarterMomentCoefficient ν τ := by
        dsimp only [C]
        simp [h3HeatThreeQuarterMomentCoefficient]

/-- The `15/4` radial weight factors as a cubic source weight times the
residual `3/4` heat weight. -/
theorem h3FourierFifteenQuarterWeight_eq_cubed_mul_threeQuarter
    (ξ : H3FourierPoint3) :
    h3FourierFifteenQuarterWeight ξ
      =
    ‖ξ‖ ^ 3 *
      h3FourierThreeQuarterWeight ξ := by
  have hξ0 : 0 ≤ ‖ξ‖ :=
    norm_nonneg ξ

  unfold
    h3FourierFifteenQuarterWeight
    h3FourierThreeQuarterWeight

  calc
    ‖ξ‖ ^ ((15 : ℝ) / 4)
        =
      ‖ξ‖ ^ ((3 : ℝ) + ((3 : ℝ) / 4)) := by
        congr 1
        ring
    _ =
      ‖ξ‖ ^ (3 : ℝ) *
        ‖ξ‖ ^ ((3 : ℝ) / 4) := by
        rw [
          Real.rpow_add_of_nonneg
            hξ0
            (by norm_num : 0 ≤ (3 : ℝ))
            (by norm_num : 0 ≤ (3 : ℝ) / 4)
        ]
    _ =
      ‖ξ‖ ^ 3 *
        ‖ξ‖ ^ ((3 : ℝ) / 4) := by
        have h3pow :
            ‖ξ‖ ^ (3 : ℝ) = ‖ξ‖ ^ (3 : ℕ) :=
          Real.rpow_natCast ‖ξ‖ 3
        rw [h3pow]

/-- Positive heat lag upgrades an `L²` amplitude with an integrable cubic raw
Fourier moment to an integrable `15/4` moment. -/
theorem h3HeatFourierSymbol_fifteenQuarter_norm_integrable_of_third
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν τ

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le hτ.le

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
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hWeightContinuous.aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable F)).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hHeat :=
    norm_h3HeatFourierSymbol_threeQuarter_le
      hν hτ ξ

  have hCube0 :
      0 ≤ ‖ξ‖ ^ 3 :=
    pow_nonneg (norm_nonneg ξ) 3

  have hTargetNonneg :
      0 ≤
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ := by
    exact
      mul_nonneg
        (Real.rpow_nonneg (norm_nonneg ξ) _)
        (norm_nonneg _)

  have hMajorNonneg :
      0 ≤
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) :=
    mul_nonneg hC0
      (mul_nonneg hCube0 (norm_nonneg _))

  have hBound :
      h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
        ≤
      C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
    rw [
      h3FourierFifteenQuarterWeight_eq_cubed_mul_threeQuarter,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 3 * h3FourierThreeQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 3 *
          (h3FourierThreeQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 3 *
                (h3FourierThreeQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hCube0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTargetNonneg,
    abs_of_nonneg hMajorNonneg
  ] using hBound

/-- Quantitative `15/4` positive-lag heat smoothing from a cubic raw Fourier
mass. -/
theorem h3HeatFourierSymbol_fifteenQuarter_norm_integral_le_of_third
    {ν τ : ℝ}
    (hν : 0 < ν)
    (hτ : 0 < τ)
    (F : H3FourierComplexL2)
    (hF3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    h3HeatThreeQuarterMomentCoefficient ν τ *
      (∫ ξ : H3FourierPoint3,
        ‖ξ‖ ^ 3 * ‖F ξ‖) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν τ

  have hTarget :=
    h3HeatFourierSymbol_fifteenQuarter_norm_integrable_of_third
      hν hτ F hF3

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (‖ξ‖ ^ 3 * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hF3.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
    intro ξ

    have hHeat :=
      norm_h3HeatFourierSymbol_threeQuarter_le
        hν hτ ξ

    have hCube0 :
        0 ≤ ‖ξ‖ ^ 3 :=
      pow_nonneg (norm_nonneg ξ) 3

    rw [
      h3FourierFifteenQuarterWeight_eq_cubed_mul_threeQuarter,
      norm_mul
    ]

    calc
      (‖ξ‖ ^ 3 * h3FourierThreeQuarterWeight ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        ‖ξ‖ ^ 3 *
          (h3FourierThreeQuarterWeight ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        ‖ξ‖ ^ 3 * C * ‖F ξ‖ := by
        have hScaled :
            ‖ξ‖ ^ 3 *
                (h3FourierThreeQuarterWeight ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            ‖ξ‖ ^ 3 * C :=
          mul_le_mul_of_nonneg_left
            hHeat hCube0

        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (‖ξ‖ ^ 3 * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  dsimp only [C] at hIntegral ⊢

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        h3HeatThreeQuarterMomentCoefficient ν τ *
          (‖ξ‖ ^ 3 * ‖F ξ‖) :=
      hIntegral
    _ =
      h3HeatThreeQuarterMomentCoefficient ν τ *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖F ξ‖) := by
      rw [integral_const_mul]

/-- Explicit `15/4` raw Fourier mass envelope for one selected midpoint-head
coordinate. -/
noncomputable def h3SelectedDuhamelHeadFifteenQuarterMomentEnvelope
    (ν A t : ℝ) : ℝ :=
  h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
    h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2)

/-- The named selected midpoint head agrees almost everywhere with positive
heat evolution of the named complete selected Duhamel raw Fourier state at
half time. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3) :
    let D : H3FourierComplexL2 :=
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
        (t := t / 2) hν U₀ hA hU₀ i
    ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
        hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
      H3FourierPoint3 → ℂ)
      =ᵐ[(volume : Measure H3FourierPoint3)]
    (fun ξ : H3FourierPoint3 =>
      h3HeatFourierSymbol ν (t / 2) ξ * D ξ) := by
  dsimp only

  let W : ℝ → H3SpectralFinVectorState :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
      hν U₀ hA hU₀

  let G : H3SpectralScalarState :=
    h3SpectralFinHeatLerayDuhamel
      ν (t / 2) hν W W i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hHeadRep :
      ((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
          hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarHeatRawRepresentative
        ν (t / 2) G := by
    dsimp only [G, W]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heatRepresentative
        hν U₀ hA hU₀ ht i

  have hDRep :
      ((D : H3FourierComplexL2) :
        H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      h3SpectralScalarRawFourier G := by
    dsimp only [
      D, G, W,
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
    ]
    rw [h3SpectralFinCoordinateRawFourierL2CLM_apply]
    exact
      h3SpectralScalarRawFourierL2_ae _

  filter_upwards [hHeadRep, hDRep] with ξ hHead hD

  rw [hHead]
  unfold h3SpectralScalarHeatRawRepresentative
  rw [hD]

/-- The named selected positive-lag Duhamel head has an integrable `15/4` raw
Fourier moment. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fifteenQuarterMoment_integrable
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
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalfR :
      t / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) htR

  have hD3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeat :=
    h3HeatFourierSymbol_fifteenQuarter_norm_integrable_of_third
      hν hhalf0 D hD3

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  refine hHeat.congr ?_
  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Quantitative `15/4` raw Fourier mass of the named selected midpoint head. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_fifteenQuarterMomentMass_le
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
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3SelectedDuhamelHeadFifteenQuarterMomentEnvelope ν A t := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hhalf0 : 0 < t / 2 := by
    positivity

  have hhalfR :
      t / 2 ≤ h3FinHeatLerayRestartRadius ν A :=
    le_trans (by linarith) htR

  have hD3 :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integrable
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hHeatBound :=
    h3HeatFourierSymbol_fifteenQuarter_norm_integral_le_of_third
      hν hhalf0 D hD3

  have hD3Bound :
      (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖)
        ≤
      h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_thirdMoment_integral_le
        hν U₀ hA hU₀ hhalf0 hhalfR i

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierFifteenQuarterWeight ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hCoeff0 :
      0 ≤ h3HeatThreeQuarterMomentCoefficient ν (t / 2) :=
    h3HeatThreeQuarterMomentCoefficient_nonneg
      hν.le hhalf0.le

  unfold h3SelectedDuhamelHeadFifteenQuarterMomentEnvelope

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierFifteenQuarterWeight ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ :=
      hIntegralEq
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
        (∫ ξ : H3FourierPoint3,
          ‖ξ‖ ^ 3 * ‖D ξ‖) :=
      hHeatBound
    _ ≤
      h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
        h3SelectedDuhamelThirdMomentEnvelope ν A (t / 2) :=
      mul_le_mul_of_nonneg_left hD3Bound hCoeff0

end
end Euclidean
end Bridge
end PrimeTensor
