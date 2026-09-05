import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Induction.MomentTail
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Duhamel.Tail.Moment.FullSecond
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Duhamel.Frechet.Fifth.Endpoint.Fourth.Duhamel.Head.Mass

/-!
# Fréchet endpoint induction: generic Duhamel moment assembly

The terminal-tail source estimate is now exponent-parametric.  This file
abstracts the remaining midpoint Duhamel bookkeeping.

There are two independent pieces.

1. **Positive-lag head smoothing.**  If the complete selected Duhamel state at
   half time has moment `q`, and the additional heat lag supplies residual
   moment `r`, then the named midpoint head has moment `q+r`.

2. **Head + tail recombination.**  If the named head and named tail both have
   moment `p`, then the complete selected Duhamel state has moment `p`, with
   the obvious sum budget.

The actual induction uses the same generic head theorem twice:

    q = n, r = 3/4   for the intermediate state n + 3/4,
    q = n, r = 1     for the next integer state n + 1.

Notice in particular that the second midpoint head needs only the original
integer `n` moment at half time; the intermediate `n+3/4` moment is needed for
the nonlinear terminal tail, not for the head.  This keeps the bootstrap
dependency graph triangular rather than circular.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SchwartzFrechetInductionMomentDuhamel
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-!
## Generic positive-lag heat lifting for quotient-safe Fourier `L²` states
-/

/-- `L²` version of the generic heat moment lift.  Unlike the source-section
version in `MomentHeatLift`, this needs only the incoming weighted `L¹` moment;
the underlying `L²` representative supplies the measurability. -/
theorem h3HeatFourierSymbol_momentLift_L2_integrable
    {q r ν τ C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖
          ≤
        C)
    (F : H3FourierComplexL2)
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      (volume : Measure H3FourierPoint3) := by
  have hqr : 0 ≤ q + r := by
    linarith

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight (q + r) ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hqr).aestronglyMeasurable.mul
      ((continuous_h3HeatFourierSymbol ν τ).aestronglyMeasurable.mul
        (MeasureTheory.Lp.aestronglyMeasurable F)).norm

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (h3FourierMomentWeight q ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFq.const_mul C

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards with ξ

  have hQ0 :
      0 ≤ h3FourierMomentWeight q ξ :=
    h3FourierMomentWeight_nonneg q ξ

  have hQR0 :
      0 ≤ h3FourierMomentWeight (q + r) ξ :=
    h3FourierMomentWeight_nonneg (q + r) ξ

  have hTarget0 :
      0 ≤
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖ :=
    mul_nonneg hQR0 (norm_nonneg _)

  have hMajor0 :
      0 ≤
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) :=
    mul_nonneg hC
      (mul_nonneg hQ0 (norm_nonneg _))

  have hFactor :
      h3FourierMomentWeight (q + r) ξ
        =
      h3FourierMomentWeight q ξ *
        h3FourierMomentWeight r ξ :=
    h3FourierMomentWeight_add hq hr ξ

  have hBound :
      h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
        ≤
      C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
    rw [norm_mul, hFactor]

    calc
      (h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierMomentWeight q ξ *
          (h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierMomentWeight q ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierMomentWeight q ξ *
                (h3FourierMomentWeight r ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierMomentWeight q ξ * C :=
          mul_le_mul_of_nonneg_left
            (hHeat ξ) hQ0
        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
        ring

  simpa only [
    Real.norm_eq_abs,
    abs_of_nonneg hTarget0,
    abs_of_nonneg hMajor0
  ] using hBound

/-- Quantitative `L²` generic heat moment lift. -/
theorem h3HeatFourierSymbol_momentLift_L2_normIntegral_le
    {q r ν τ C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖
          ≤
        C)
    (F : H3FourierComplexL2)
    (hFq :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖F ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
      ≤
    C *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ * ‖F ξ‖) := by
  have hTarget :=
    h3HeatFourierSymbol_momentLift_L2_integrable
      hq hr hC hHeat F hFq

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          C * (h3FourierMomentWeight q ξ * ‖F ξ‖))
        (volume : Measure H3FourierPoint3) :=
    hFq.const_mul C

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
            ‖h3HeatFourierSymbol ν τ ξ * F ξ‖
          ≤
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
    intro ξ

    have hQ0 :
        0 ≤ h3FourierMomentWeight q ξ :=
      h3FourierMomentWeight_nonneg q ξ

    have hFactor :
        h3FourierMomentWeight (q + r) ξ
          =
        h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ :=
      h3FourierMomentWeight_add hq hr ξ

    rw [norm_mul, hFactor]

    calc
      (h3FourierMomentWeight q ξ *
          h3FourierMomentWeight r ξ) *
          (‖h3HeatFourierSymbol ν τ ξ‖ * ‖F ξ‖)
          =
        h3FourierMomentWeight q ξ *
          (h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν τ ξ‖) *
          ‖F ξ‖ := by
        ring
      _ ≤
        h3FourierMomentWeight q ξ * C * ‖F ξ‖ := by
        have hScaled :
            h3FourierMomentWeight q ξ *
                (h3FourierMomentWeight r ξ *
                  ‖h3HeatFourierSymbol ν τ ξ‖)
              ≤
            h3FourierMomentWeight q ξ * C :=
          mul_le_mul_of_nonneg_left
            (hHeat ξ) hQ0
        exact
          mul_le_mul_of_nonneg_right
            hScaled
            (norm_nonneg (F ξ))
      _ =
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) := by
        ring

  have hIntegral :=
    integral_mono hTarget hMajor hPoint

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν τ ξ * F ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        C * (h3FourierMomentWeight q ξ * ‖F ξ‖) :=
      hIntegral
    _ =
      C *
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight q ξ * ‖F ξ‖) := by
      rw [integral_const_mul]

/-!
## Generic midpoint-head transfer
-/

/-- If the complete selected Duhamel state at half time carries moment `q`,
and the positive half-time heat lag supplies residual moment `r`, then the
named midpoint head carries moment `q+r`. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integrable_of_halfDuhamelMoment
    {q r ν A t C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight (q + r) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hDq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDq

  have hLift :=
    h3HeatFourierSymbol_momentLift_L2_integrable
      hq hr hC hHeat D hDq'

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  refine hLift.congr ?_
  filter_upwards [hRep] with ξ hξ
  rw [hξ]

/-- Quantitative generic midpoint-head moment transfer. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integral_le_of_halfDuhamelMoment
    {q r ν A t C : ℝ}
    (hq : 0 ≤ q)
    (hr : 0 ≤ r)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hC : 0 ≤ C)
    (hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight r ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    C *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t / 2) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖) := by
  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t / 2) hν U₀ hA hU₀ i

  have hDq' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact hDq

  have hLift :=
    h3HeatFourierSymbol_momentLift_L2_normIntegral_le
      hq hr hC hHeat D hDq'

  have hRep :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_ae_eq_heat_mul_halfDuhamelRawFourierL2
      hν U₀ hA hU₀ ht i

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight (q + r) ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + r) ξ *
          ‖h3HeatFourierSymbol ν (t / 2) ξ * D ξ‖ := by
    apply integral_congr_ae
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  dsimp only [D] at hLift ⊢
  exact hIntegralEq.trans_le hLift

/-!
## The two residuals used by the Nat induction
-/

/-- Intermediate midpoint head: `q -> q + 3/4`. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_addThreeQuarterMoment_integrable_of_halfDuhamelMoment
    {q ν A t : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight (q + (3 : ℝ) / 4) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν (t / 2)

  have hhalf : 0 < t / 2 := by
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le hhalf.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierThreeQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_threeQuarter_le
        hν hhalf ξ)

  exact
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integrable_of_halfDuhamelMoment
      hq
      (by norm_num : 0 ≤ (3 : ℝ) / 4)
      hν U₀ hA hU₀ ht i
      hC0 hHeat hDq

/-- Quantitative intermediate midpoint-head estimate. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_addThreeQuarterMoment_integral_le_of_halfDuhamelMoment
    {q ν A t : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + (3 : ℝ) / 4) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatThreeQuarterMomentCoefficient ν (t / 2) *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t / 2) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖) := by
  let C : ℝ :=
    h3HeatThreeQuarterMomentCoefficient ν (t / 2)

  have hhalf : 0 < t / 2 := by
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatThreeQuarterMomentCoefficient_nonneg
        hν.le hhalf.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight ((3 : ℝ) / 4) ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      h3FourierThreeQuarterWeight
    ] using
      (norm_h3HeatFourierSymbol_threeQuarter_le
        hν hhalf ξ)

  have hBase :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integral_le_of_halfDuhamelMoment
      hq
      (by norm_num : 0 ≤ (3 : ℝ) / 4)
      hν U₀ hA hU₀ ht i
      hC0 hHeat hDq

  simpa only [C] using hBase

/-- Integer midpoint head: `q -> q + 1`. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_addOneMoment_integrable_of_halfDuhamelMoment
    {q ν A t : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight (q + 1) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let C : ℝ :=
    h3HeatOneMomentCoefficient ν (t / 2)

  have hhalf : 0 < t / 2 := by
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatOneMomentCoefficient_nonneg
        hν.le hhalf.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (1 : ℝ) ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      Real.rpow_one
    ] using
      (norm_h3HeatFourierSymbol_oneMoment_le
        hν hhalf ξ)

  exact
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integrable_of_halfDuhamelMoment
      hq
      (by norm_num : 0 ≤ (1 : ℝ))
      hν U₀ hA hU₀ ht i
      hC0 hHeat hDq

/-- Quantitative integer midpoint-head estimate. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_addOneMoment_integral_le_of_halfDuhamelMoment
    {q ν A t : ℝ}
    (hq : 0 ≤ q)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hDq :
      let D : H3FourierComplexL2 :=
        h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
          (t := t / 2) hν U₀ hA hU₀ i
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight q ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3)) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight (q + 1) ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
              hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    h3HeatOneMomentCoefficient ν (t / 2) *
      (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight q ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t / 2) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖) := by
  let C : ℝ :=
    h3HeatOneMomentCoefficient ν (t / 2)

  have hhalf : 0 < t / 2 := by
    positivity

  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      h3HeatOneMomentCoefficient_nonneg
        hν.le hhalf.le

  have hHeat :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight (1 : ℝ) ξ *
            ‖h3HeatFourierSymbol ν (t / 2) ξ‖
          ≤
        C := by
    intro ξ
    dsimp only [C]
    simpa only [
      h3FourierMomentWeight,
      Real.rpow_one
    ] using
      (norm_h3HeatFourierSymbol_oneMoment_le
        hν hhalf ξ)

  have hBase :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2_moment_integral_le_of_halfDuhamelMoment
      hq
      (by norm_num : 0 ≤ (1 : ℝ))
      hν U₀ hA hU₀ ht i
      hC0 hHeat hDq

  simpa only [C] using hBase

/-!
## Generic head + tail recombination
-/

/-- Generic moment integrability of the complete selected Duhamel state from
the same moment on its named head and tail pieces. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integrable_of_head_tail
    {p ν A t : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hHead :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3)) :
    Integrable
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      (volume : Measure H3FourierPoint3) := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ ht i

  let T : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hHead' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact hHead

  have hTail' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact hTail

  have hMajor :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖ +
            h3FourierMomentWeight p ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead'.add hTail'

  have hTargetMeas :
      AEStronglyMeasurable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) :=
    (continuous_h3FourierMomentWeight hp).aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable D).norm

  have hRep :
      ((D : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [D, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ ht i

  refine hMajor.mono' hTargetMeas ?_
  filter_upwards [hRep] with ξ hξ

  have hw :
      0 ≤ h3FourierMomentWeight p ξ :=
    h3FourierMomentWeight_nonneg p ξ

  have hTarget0 :
      0 ≤ h3FourierMomentWeight p ξ * ‖D ξ‖ :=
    mul_nonneg hw (norm_nonneg _)

  rw [Real.norm_eq_abs, abs_of_nonneg hTarget0]
  rw [hξ]

  calc
    h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖
        ≤
      h3FourierMomentWeight p ξ * (‖H ξ‖ + ‖T ξ‖) :=
      mul_le_mul_of_nonneg_left
        (norm_add_le (H ξ) (T ξ))
        hw
    _ =
      h3FourierMomentWeight p ξ * ‖H ξ‖ +
        h3FourierMomentWeight p ξ * ‖T ξ‖ := by
      ring

/-- Quantitative generic complete-Duhamel moment estimate from independent
head and tail budgets. -/
theorem h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integral_le_of_head_tail
    {p ν A t BHead BTail : ℝ}
    (hp : 0 ≤ p)
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (i : Fin 3)
    (hHead :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hTail :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        (volume : Measure H3FourierPoint3))
    (hHeadLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
                hν U₀ hA hU₀ ht i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤ BHead)
    (hTailLe :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ *
            ‖((h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
                (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
              H3FourierPoint3 → ℂ) ξ‖)
        ≤ BTail) :
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ *
          ‖((h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
              (t := t) hν U₀ hA hU₀ i : H3FourierComplexL2) :
            H3FourierPoint3 → ℂ) ξ‖)
      ≤
    BHead + BTail := by
  let H : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedHeadRawFourierL2
      hν U₀ hA hU₀ ht i

  let T : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedTailRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  let D : H3FourierComplexL2 :=
    h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2
      (t := t) hν U₀ hA hU₀ i

  have hHead' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [H]
    exact hHead

  have hTail' :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [T]
    exact hTail

  have hFull :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        (volume : Measure H3FourierPoint3) := by
    dsimp only [D]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_moment_integrable_of_head_tail
        hp hν U₀ hA hU₀ ht i hHead hTail

  have hRep :
      ((D : H3FourierComplexL2) : H3FourierPoint3 → ℂ)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 => H ξ + T ξ) := by
    dsimp only [D, H, T]
    exact
      h3SpectralFinHeatLerayDuhamelSelectedRawFourierL2_ae_eq_head_add_tail
        hν U₀ hA hU₀ ht i

  have hWeightedRep :
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ * ‖D ξ‖)
        =ᵐ[(volume : Measure H3FourierPoint3)]
      (fun ξ : H3FourierPoint3 =>
        h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖) := by
    filter_upwards [hRep] with ξ hξ
    rw [hξ]

  have hSumInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hFull.congr hWeightedRep

  have hMajorInt :
      Integrable
        (fun ξ : H3FourierPoint3 =>
          h3FourierMomentWeight p ξ * ‖H ξ‖ +
            h3FourierMomentWeight p ξ * ‖T ξ‖)
        (volume : Measure H3FourierPoint3) :=
    hHead'.add hTail'

  have hPoint :
      ∀ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖T ξ‖ := by
    intro ξ

    have hw :
        0 ≤ h3FourierMomentWeight p ξ :=
      h3FourierMomentWeight_nonneg p ξ

    calc
      h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖
          ≤
        h3FourierMomentWeight p ξ * (‖H ξ‖ + ‖T ξ‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le (H ξ) (T ξ))
          hw
      _ =
        h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖T ξ‖ := by
        ring

  have hMono :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖)
        ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖T ξ‖) :=
    integral_mono hSumInt hMajorInt hPoint

  have hIntegralEq :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖ :=
    integral_congr_ae hWeightedRep

  have hHeadLe' :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ‖)
        ≤ BHead := by
    dsimp only [H]
    exact hHeadLe

  have hTailLe' :
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖T ξ‖)
        ≤ BTail := by
    dsimp only [T]
    exact hTailLe

  calc
    (∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖D ξ‖)
        =
      ∫ ξ : H3FourierPoint3,
        h3FourierMomentWeight p ξ * ‖H ξ + T ξ‖ :=
      hIntegralEq
    _ ≤
      ∫ ξ : H3FourierPoint3,
        (h3FourierMomentWeight p ξ * ‖H ξ‖ +
          h3FourierMomentWeight p ξ * ‖T ξ‖) :=
      hMono
    _ =
      (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖H ξ‖) +
        (∫ ξ : H3FourierPoint3,
          h3FourierMomentWeight p ξ * ‖T ξ‖) := by
      rw [integral_add hHead' hTail']
    _ ≤
      BHead + BTail :=
      add_le_add hHeadLe' hTailLe'

end
end Euclidean
end Bridge
end PrimeTensor
