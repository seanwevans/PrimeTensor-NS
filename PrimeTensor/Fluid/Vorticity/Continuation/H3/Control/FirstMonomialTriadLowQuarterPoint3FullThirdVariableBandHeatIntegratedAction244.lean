import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdVariableBandHeatTimeWindow244
import Mathlib.Tactic

/-!
# Exact temporal integral of the two-band heat concentration source

Previous checkpoints identified spectral two-band data with a near-Young gap
at most `1/n` yet a positive initial signed heat source at least `n/128`.
A large derivative alone cannot guarantee a large temporal accumulation.

This file proves that the HEAT-ONLY two-band gap has derivative exactly
minus the previously identified six-moment heat production rate.  Its
interval integral is therefore the actual finite-time gap decrease, bounded
by `1/n` on every forward window. This is calculus on an algebraic two-band
heat orbit, not a nonlinear Navier--Stokes continuation statement.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace Interval

noncomputable section
set_option maxHeartbeats 2400000

/-- Derivative of a general two-band Young gap with respect to high-band mass.
The exact numerator involves x²-r⁴y², exposing the barycenter sign threshold. -/
theorem h3_twoBandYoungGap_hasDerivAt_highMass244
    (r x y : ℝ) (hr : 0 ≤ r) (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => h3TwoBandVariableYoungGap244 r x z)
      (x * (r ^ 2 - 1) ^ 2 * (x ^ 2 - r ^ 4 * y ^ 2) /
        ((x + y) * (x + r ^ 4 * y)) ^ 2) y := by
  have h0 : HasDerivAt (fun z : ℝ => x + z) 1 y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_add x
  have h2 : HasDerivAt (fun z : ℝ => x + r ^ 2 * z) (r ^ 2) y := by
    simpa using ((hasDerivAt_id y).const_mul (r ^ 2)).const_add x
  have h4 : HasDerivAt (fun z : ℝ => x + r ^ 4 * z) (r ^ 4) y := by
    simpa using ((hasDerivAt_id y).const_mul (r ^ 4)).const_add x
  have hDen : (x + y) * (x + r ^ 4 * y) ≠ 0 := by
    have hFourth : 0 ≤ r ^ 4 * y :=
      mul_nonneg (pow_nonneg hr 4) hy.le
    exact ne_of_gt (mul_pos (add_pos hx hy)
      (by linarith only [hx, hFourth]))
  have hVar := h3_normalizedFourierVariance_hasDerivAt244
    (fun z : ℝ => x + z)
    (fun z : ℝ => x + r ^ 2 * z)
    (fun z : ℝ => x + r ^ 4 * z)
    y 1 (r ^ 2) (r ^ 4) h0 h2 h4 hDen
  have hCoefficient :
      (((x + r ^ 2 * y) ^ 2 *
          (1 * (x + r ^ 4 * y) + (x + y) * r ^ 4) -
        2 * (x + r ^ 2 * y) * r ^ 2 *
          ((x + y) * (x + r ^ 4 * y))) /
        ((x + y) * (x + r ^ 4 * y)) ^ 2) =
      x * (r ^ 2 - 1) ^ 2 * (x ^ 2 - r ^ 4 * y ^ 2) /
        ((x + y) * (x + r ^ 4 * y)) ^ 2 := by
    ring
  change HasDerivAt
    (fun z : ℝ => 1 - (x + r ^ 2 * z) ^ 2 /
      ((x + z) * (x + r ^ 4 * z))) _ y
  exact hVar.congr_deriv hCoefficient

/-- The high-band relative mass follows a scalar linear heat ODE. -/
theorem h3_twoBandNearYoungHeat_relativeMass_hasDerivAt244
    (n t : ℝ) :
    HasDerivAt (h3TwoBandNearYoungHeatRelativeHighMass244 n)
      ((-2 : ℝ) * (n ^ 2 - 1) *
        h3TwoBandNearYoungHeatRelativeHighMass244 n t) t := by
  let c : ℝ := (-2 : ℝ) * (n ^ 2 - 1)
  have hLinear : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul c
  have hExp : HasDerivAt (fun s : ℝ => Real.exp (c * s))
      (Real.exp (c * t) * c) t := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (c * t)).comp t hLinear
  change HasDerivAt (fun s : ℝ => Real.exp (c * s))
    (c * Real.exp (c * t)) t
  exact hExp.congr_deriv (mul_comm _ _)

/-- Exact identity: the negative derivative of the HEAT gap equals the
signed instantaneous six-moment heat-concentration production. -/
theorem h3_twoBandNearYoungHeat_gap_hasDerivAt244
    (n t : ℝ) (hn : 2 ≤ n) :
    HasDerivAt (h3TwoBandNearYoungHeatGapAt244 n)
      (-h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9)
        (h3TwoBandNearYoungHeatRelativeHighMass244 n t)) t := by
  have hnPos : 0 < n := by linarith only [hn]
  have hyPos : 0 < h3TwoBandNearYoungHeatRelativeHighMass244 n t := by
    unfold h3TwoBandNearYoungHeatRelativeHighMass244
    exact Real.exp_pos _
  have hGap := h3_twoBandYoungGap_hasDerivAt_highMass244
    (n ^ 2) (n ^ 9) (h3TwoBandNearYoungHeatRelativeHighMass244 n t)
    (pow_nonneg hnPos.le 2) (pow_pos hnPos 9) hyPos
  have hY := h3_twoBandNearYoungHeat_relativeMass_hasDerivAt244 n t
  have hChain : HasDerivAt (h3TwoBandNearYoungHeatGapAt244 n)
      (( (n ^ 9) * ((n ^ 2) ^ 2 - 1) ^ 2 *
          ((n ^ 9) ^ 2 - (n ^ 2) ^ 4 *
            (h3TwoBandNearYoungHeatRelativeHighMass244 n t) ^ 2) /
          (((n ^ 9) + h3TwoBandNearYoungHeatRelativeHighMass244 n t) *
            ((n ^ 9) + (n ^ 2) ^ 4 *
              h3TwoBandNearYoungHeatRelativeHighMass244 n t)) ^ 2) *
        ((-2 : ℝ) * (n ^ 2 - 1) *
          h3TwoBandNearYoungHeatRelativeHighMass244 n t)) t := by
    change HasDerivAt
      (fun s => h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9)
        (h3TwoBandNearYoungHeatRelativeHighMass244 n s)) _ t
    exact hGap.comp t hY
  have hRateEq :
      (( (n ^ 9) * ((n ^ 2) ^ 2 - 1) ^ 2 *
          ((n ^ 9) ^ 2 - (n ^ 2) ^ 4 *
            (h3TwoBandNearYoungHeatRelativeHighMass244 n t) ^ 2) /
          (((n ^ 9) + h3TwoBandNearYoungHeatRelativeHighMass244 n t) *
            ((n ^ 9) + (n ^ 2) ^ 4 *
              h3TwoBandNearYoungHeatRelativeHighMass244 n t)) ^ 2) *
        ((-2 : ℝ) * (n ^ 2 - 1) *
          h3TwoBandNearYoungHeatRelativeHighMass244 n t)) =
      -h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9)
        (h3TwoBandNearYoungHeatRelativeHighMass244 n t) := by
    rw [h3_twoBandVariableHeat_rate_eq_factor244]
    ring
  rw [← hRateEq]
  exact hChain

/-- The instantaneous signed production along the heat orbit. -/
noncomputable def h3TwoBandNearYoungHeatProductionAt244 (n t : ℝ) : ℝ :=
  h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9)
    (h3TwoBandNearYoungHeatRelativeHighMass244 n t)

/-- A convenient primitive of the production rate. -/
noncomputable def h3TwoBandNearYoungHeatProductionPrimitive244
    (n t : ℝ) : ℝ :=
  -h3TwoBandNearYoungHeatGapAt244 n t

/-- The primitive has derivative equal to the exact heat rate at every time. -/
theorem h3_twoBandNearYoungHeat_primitive_hasDerivAt244
    (n t : ℝ) (hn : 2 ≤ n) :
    HasDerivAt (h3TwoBandNearYoungHeatProductionPrimitive244 n)
      (h3TwoBandNearYoungHeatProductionAt244 n t) t := by
  have h := (h3_twoBandNearYoungHeat_gap_hasDerivAt244 n t hn).neg
  have hPrimitive :
      h3TwoBandNearYoungHeatProductionPrimitive244 n =
        -h3TwoBandNearYoungHeatGapAt244 n := by
    funext s
    rfl
  rw [hPrimitive]
  simpa only [h3TwoBandNearYoungHeatProductionAt244, neg_neg] using h

/-- The exact production rate is globally continuous, so every finite
interval integral is legitimate. -/
theorem h3_twoBandNearYoungHeat_production_continuous244
    (n : ℝ) (hn : 2 ≤ n) :
    Continuous (h3TwoBandNearYoungHeatProductionAt244 n) := by
  have hY : Continuous (h3TwoBandNearYoungHeatRelativeHighMass244 n) := by
    unfold h3TwoBandNearYoungHeatRelativeHighMass244
    fun_prop
  have hNumerator : Continuous (fun t : ℝ =>
      2 * ((n ^ 9) + (n ^ 2) ^ 2 *
        h3TwoBandNearYoungHeatRelativeHighMass244 n t) *
        h3GlobalRadialHeatBarycenterImbalance244
          ((n ^ 9) + h3TwoBandNearYoungHeatRelativeHighMass244 n t)
          ((n ^ 9) + (n ^ 2) * h3TwoBandNearYoungHeatRelativeHighMass244 n t)
          ((n ^ 9) + (n ^ 2) ^ 2 * h3TwoBandNearYoungHeatRelativeHighMass244 n t)
          ((n ^ 9) + (n ^ 2) ^ 3 * h3TwoBandNearYoungHeatRelativeHighMass244 n t)
          ((n ^ 9) + (n ^ 2) ^ 4 * h3TwoBandNearYoungHeatRelativeHighMass244 n t)
          ((n ^ 9) + (n ^ 2) ^ 5 * h3TwoBandNearYoungHeatRelativeHighMass244 n t)) := by
    unfold h3GlobalRadialHeatBarycenterImbalance244
    fun_prop
  have hDenominator : Continuous (fun t : ℝ =>
      (((n ^ 9) + h3TwoBandNearYoungHeatRelativeHighMass244 n t) *
        ((n ^ 9) + (n ^ 2) ^ 4 *
          h3TwoBandNearYoungHeatRelativeHighMass244 n t)) ^ 2) := by
    fun_prop
  unfold h3TwoBandNearYoungHeatProductionAt244 h3TwoBandVariableHeatRate244
  apply hNumerator.div hDenominator
  intro t
  have hnPos : 0 < n := by linarith only [hn]
  have hyPos : 0 < h3TwoBandNearYoungHeatRelativeHighMass244 n t := by
    unfold h3TwoBandNearYoungHeatRelativeHighMass244
    exact Real.exp_pos _
  have hLeft : 0 < (n ^ 9) + h3TwoBandNearYoungHeatRelativeHighMass244 n t :=
    add_pos (pow_pos hnPos 9) hyPos
  have hRight : 0 < (n ^ 9) + (n ^ 2) ^ 4 *
      h3TwoBandNearYoungHeatRelativeHighMass244 n t := by
    have hAdd : 0 ≤ (n ^ 2) ^ 4 *
        h3TwoBandNearYoungHeatRelativeHighMass244 n t := by positivity
    linarith only [pow_pos hnPos 9, hAdd]
  exact ne_of_gt (pow_pos (mul_pos hLeft hRight) 2)

/-- Fundamental theorem of calculus for the true two-band HEAT rate.
This is no longer merely a finite-difference / monotonicity statement. -/
theorem h3_twoBandNearYoungHeat_production_integral_eq_gap_drop244
    (n s t : ℝ) (hn : 2 ≤ n) :
    (∫ τ in s..t, h3TwoBandNearYoungHeatProductionAt244 n τ) =
      h3TwoBandNearYoungHeatGapAt244 n s -
        h3TwoBandNearYoungHeatGapAt244 n t := by
  let F : ℝ → ℝ := h3TwoBandNearYoungHeatProductionPrimitive244 n
  have hDerivative (τ : ℝ) :
      HasDerivAt F (h3TwoBandNearYoungHeatProductionAt244 n τ) τ :=
    h3_twoBandNearYoungHeat_primitive_hasDerivAt244 n τ hn
  have hDiff : ∀ τ : ℝ, τ ∈ Set.uIcc s t → DifferentiableAt ℝ F τ := by
    intro τ _
    exact (hDerivative τ).differentiableAt
  have hDeriv : deriv F = h3TwoBandNearYoungHeatProductionAt244 n := by
    funext τ
    exact (hDerivative τ).deriv
  have hInt : IntervalIntegrable (deriv F) volume s t := by
    rw [hDeriv]
    exact (h3_twoBandNearYoungHeat_production_continuous244 n hn).intervalIntegrable s t
  have hFTC := intervalIntegral.integral_deriv_eq_sub hDiff hInt
  rw [hDeriv] at hFTC
  dsimp only [F, h3TwoBandNearYoungHeatProductionPrimitive244] at hFTC
  linarith only [hFTC]

/-- The entire finite-time integrated heat production is bounded by the
initial Young gap, even as its instantaneous value becomes unbounded. -/
theorem h3_twoBandNearYoungHeat_integratedProduction_le_inverse244
    (n s t : ℝ) (hn : 2 ≤ n) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ (∫ τ in s..t, h3TwoBandNearYoungHeatProductionAt244 n τ) ∧
      (∫ τ in s..t, h3TwoBandNearYoungHeatProductionAt244 n τ) ≤ 1 / n := by
  rw [h3_twoBandNearYoungHeat_production_integral_eq_gap_drop244 n s t hn]
  have hMon := h3_twoBandNearYoungHeat_gap_antitone244 n s t hn hs hst
  have hAt0 := h3_twoBandNearYoungHeat_gap_antitone244 n 0 s hn le_rfl hs
  have hNonneg := h3_twoBandNearYoungHeat_gap_nonneg244 n t hn (le_trans hs hst)
  have hInitial := h3_twoBandNearYoungHeat_gap_initial244 n
  have hYoung := h3_twoBandNearYoung_gap_le_inverse244 n hn
  rw [← hInitial] at hYoung
  constructor <;> linarith only [hMon, hAt0, hNonneg, hYoung]

/-- A uniform integrated source budget is compatible with an unbounded
instantaneous initial source. No nonlinear Navier--Stokes inference is made. -/
theorem h3_twoBandNearYoungHeat_largeInitialRate_boundedIntegrated244
    (n : ℝ) (hn : 2 ≤ n) :
    n / 128 ≤ h3TwoBandNearYoungHeatProductionAt244 n 0 ∧
      ∀ t : ℝ, 0 ≤ t →
        0 ≤ (∫ τ in (0 : ℝ)..t, h3TwoBandNearYoungHeatProductionAt244 n τ) ∧
        (∫ τ in (0 : ℝ)..t, h3TwoBandNearYoungHeatProductionAt244 n τ) ≤ 1 / n := by
  have hInitial : h3TwoBandNearYoungHeatProductionAt244 n 0 =
      h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9) 1 := by
    simp [h3TwoBandNearYoungHeatProductionAt244,
      h3TwoBandNearYoungHeatRelativeHighMass244]
  constructor
  · rw [hInitial]
    exact h3_twoBandNearYoung_heatRate_ge_linear244 n hn
  · intro t ht
    exact h3_twoBandNearYoungHeat_integratedProduction_le_inverse244
      n 0 t hn le_rfl ht

end
end PrimeTensor.FirstMonomialTriad
