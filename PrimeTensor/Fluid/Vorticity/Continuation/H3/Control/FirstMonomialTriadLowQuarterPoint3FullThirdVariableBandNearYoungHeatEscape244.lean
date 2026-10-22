import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdVariableBandHeatEscape244
import Mathlib.Tactic

/-!
# A simultaneous near-Young and unbounded instantaneous heat-rate test

The previous two-band counterexample kept the low moments bounded while
its signed heat source grew, but did not force the normalized Young gap to
zero. Here the second radial weight is `q=n²` and its unscaled spectral
masses are `x=n⁹, y=1`, for `n≥2`.  Homogeneity allows the equivalent
bounded-moment masses `x=1, y=n⁻⁹`.

  R(n) = n (n⁴ - 1)² / ((n⁹+1)(n+1)) <= 1/n;
  B(n) = 2n (n¹⁰-1)(n²-1)³(n²+1)² / ((n⁹+1)²(n+1)²)
       >= n/128.

Thus in the algebraic spectral test R tends to 0 and B diverges, while
all of m0, m2, m4 lie between 1 and 2 after rescaling. These are not
actual smooth NS trajectories; the result rules out a universal pointwise
heat-rate ceiling deduced solely from lower moments and near-Young gap.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

/-- Algebraic normalized two-band Young gap for frequency weights 1,r. -/
noncomputable def h3TwoBandVariableYoungGap244 (r x y : ℝ) : ℝ :=
  1 - (x + r ^ 2 * y) ^ 2 / ((x + y) * (x + r ^ 4 * y))

/-- Exact Young gap for two spectral atoms, with strictly positive
normalizing mass. The gap vanishes only if a band disappears or r=1. -/
theorem h3_twoBandVariableYoungGap_eq_variance244
    (r x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : 0 ≤ r) :
    h3TwoBandVariableYoungGap244 r x y =
      x * y * (r ^ 2 - 1) ^ 2 / ((x + y) * (x + r ^ 4 * y)) := by
  have hDen : (x + y) * (x + r ^ 4 * y) ≠ 0 := by
    have hSum : 0 < x + y := add_pos hx hy
    have hFourth : 0 ≤ r ^ 4 := pow_nonneg hr 4
    have hOther : 0 < x + r ^ 4 * y := by
      have hNonneg : 0 ≤ r ^ 4 * y := mul_nonneg hFourth hy.le
      linarith only [hx, hNonneg]
    exact ne_of_gt (mul_pos hSum hOther)
  unfold h3TwoBandVariableYoungGap244
  field_simp [hDen]
  <;> ring

/-- Close-form near-Young gap of the r=n², x=n⁹, y=1 family. -/
theorem h3_twoBandNearYoung_gap_closed244
    (n : ℝ) (hn : 2 ≤ n) :
    h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9) 1 =
      n * (n ^ 4 - 1) ^ 2 / ((n ^ 9 + 1) * (n + 1)) := by
  have hnPos : 0 < n := by linarith only [hn]
  rw [h3_twoBandVariableYoungGap_eq_variance244
    (n ^ 2) (n ^ 9) 1 (pow_pos hnPos 9) (by norm_num)
    (pow_nonneg hnPos.le 2)]
  have hn0 : n ≠ 0 := ne_of_gt hnPos
  have hSum : n ^ 9 + 1 ≠ 0 := by positivity
  have hNp1 : n + 1 ≠ 0 := by positivity
  have hTop : n ^ 9 + n ^ 8 ≠ 0 := by positivity
  field_simp [hn0, hSum, hNp1, hTop]
  <;> ring

/-- Explicit rate for this very same small-Young-gap family. -/
theorem h3_twoBandNearYoung_heatRate_closed244
    (n : ℝ) (hn : 2 ≤ n) :
    h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9) 1 =
      (2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 *
        (n ^ 2 + 1) ^ 2) /
        ((n ^ 9 + 1) ^ 2 * (n + 1) ^ 2) := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244]
  have hnPos : 0 < n := by linarith only [hn]
  have hn0 : n ≠ 0 := ne_of_gt hnPos
  have hSum : n ^ 9 + 1 ≠ 0 := by positivity
  have hNp1 : n + 1 ≠ 0 := by positivity
  have hTop : n ^ 9 + n ^ 8 ≠ 0 := by positivity
  field_simp [hn0, hSum, hNp1, hTop]
  <;> ring

/-- The normalized Young gap is small; no spectral compactness condition
is assumed here. -/
theorem h3_twoBandNearYoung_gap_le_inverse244
    (n : ℝ) (hn : 2 ≤ n) :
    h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9) 1 ≤ 1 / n := by
  rw [h3_twoBandNearYoung_gap_closed244 n hn]
  have hnPos : 0 < n := by linarith only [hn]
  have hn1 : 1 ≤ n := by linarith only [hn]
  have h4 : 1 ≤ n ^ 4 := by
    calc
      (1 : ℝ) = 1 ^ 4 := by norm_num
      _ ≤ n ^ 4 := by gcongr <;> exact hn1
  have hSq : (n ^ 4 - 1) ^ 2 ≤ (n ^ 4) ^ 2 := by
    have hDiff : 0 ≤ n ^ 4 - 1 := by linarith only [h4]
    gcongr <;> linarith only [h4]
  have hNum : n ^ 2 * (n ^ 4 - 1) ^ 2 ≤ n ^ 10 := by
    calc
      n ^ 2 * (n ^ 4 - 1) ^ 2 ≤ n ^ 2 * (n ^ 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hSq (pow_nonneg hnPos.le 2)
      _ = n ^ 10 := by ring
  have hDenLower : n ^ 10 ≤ (n ^ 9 + 1) * (n + 1) := by
    calc
      n ^ 10 ≤ n ^ 10 + n ^ 9 + n + 1 := by
        have h9 : 0 ≤ n ^ 9 := pow_nonneg hnPos.le 9
        linarith only [h9, hnPos.le]
      _ = (n ^ 9 + 1) * (n + 1) := by ring
  have hDenPos : 0 < (n ^ 9 + 1) * (n + 1) := by positivity
  have hNumN : (n * (n ^ 4 - 1) ^ 2) * n ≤
      (n ^ 9 + 1) * (n + 1) := by
    calc
      (n * (n ^ 4 - 1) ^ 2) * n = n ^ 2 * (n ^ 4 - 1) ^ 2 := by ring
      _ ≤ n ^ 10 := hNum
      _ ≤ (n ^ 9 + 1) * (n + 1) := hDenLower
  apply (div_le_iff₀ hDenPos).2
  calc
    n * (n ^ 4 - 1) ^ 2 ≤ ((n ^ 9 + 1) * (n + 1)) / n :=
      (le_div_iff₀ hnPos).2 hNumN
    _ = (1 / n) * ((n ^ 9 + 1) * (n + 1)) := by ring

/-- The positive instantaneous heat source grows at least linearly while
the normalized Young gap tends to zero. -/
theorem h3_twoBandNearYoung_heatRate_ge_linear244
    (n : ℝ) (hn : 2 ≤ n) :
    n / 128 ≤ h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9) 1 := by
  rw [h3_twoBandNearYoung_heatRate_closed244 n hn]
  have hnPos : 0 < n := by linarith only [hn]
  have hn1 : 1 ≤ n := by linarith only [hn]
  have h2 : 2 ≤ n ^ 2 := by
    calc
      (2 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ n ^ 2 := by gcongr <;> exact hn
  have h10 : 2 ≤ n ^ 10 := by
    calc
      (2 : ℝ) ≤ 2 ^ 10 := by norm_num
      _ ≤ n ^ 10 := by gcongr <;> exact hn
  have hGap : n ^ 2 / 2 ≤ n ^ 2 - 1 := by
    linarith only [h2]
  have hGapNonneg : 0 ≤ n ^ 2 - 1 := by linarith only [h2]
  have hTenth : n ^ 10 / 2 ≤ n ^ 10 - 1 := by
    linarith only [h10]
  have hThird : (n ^ 2 / 2) ^ 3 ≤ (n ^ 2 - 1) ^ 3 := by
    gcongr <;> exact hGap
  have hExtra : n ^ 2 ≤ n ^ 2 + 1 := by linarith
  have hExtraSq : (n ^ 2) ^ 2 ≤ (n ^ 2 + 1) ^ 2 := by
    gcongr <;> exact hExtra
  have hTenthNonneg : 0 ≤ n ^ 10 - 1 := by
    linarith only [h10]
  have hTenthFactorNonneg : 0 ≤ 2 * n * (n ^ 10 - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) hnPos.le) hTenthNonneg
  have hLargeFactorNonneg :
      0 ≤ 2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 :=
    mul_nonneg hTenthFactorNonneg (pow_nonneg hGapNonneg 3)
  have hLowerNum : n ^ 21 / 8 ≤
      2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 * (n ^ 2 + 1) ^ 2 := by
    calc
      n ^ 21 / 8 =
          2 * n * (n ^ 10 / 2) * (n ^ 2 / 2) ^ 3 * (n ^ 2) ^ 2 := by ring
      _ ≤ 2 * n * (n ^ 10 - 1) * (n ^ 2 / 2) ^ 3 *
          (n ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hTenth (by positivity)
          · positivity
        · positivity
      _ ≤ 2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 *
          (n ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hThird hTenthFactorNonneg
        · positivity
      _ ≤ 2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 *
          (n ^ 2 + 1) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hExtraSq hLargeFactorNonneg
  have hNinth : 1 ≤ n ^ 9 := by
    calc
      (1 : ℝ) = 1 ^ 9 := by norm_num
      _ ≤ n ^ 9 := by gcongr <;> exact hn1
  have hDenOne : n ^ 9 + 1 ≤ 2 * n ^ 9 := by
    linarith only [hNinth]
  have hDenTwo : n + 1 ≤ 2 * n := by
    linarith only [hn1]
  have hDenSq : (n ^ 9 + 1) ^ 2 * (n + 1) ^ 2 ≤ 16 * n ^ 20 := by
    calc
      (n ^ 9 + 1) ^ 2 * (n + 1) ^ 2 ≤
          (2 * n ^ 9) ^ 2 * (2 * n) ^ 2 := by
        gcongr <;> first | exact hDenOne | exact hDenTwo | positivity
      _ = 16 * n ^ 20 := by ring
  have hDenPos : 0 < (n ^ 9 + 1) ^ 2 * (n + 1) ^ 2 := by positivity
  apply (le_div_iff₀ hDenPos).2
  calc
    (n / 128) * ((n ^ 9 + 1) ^ 2 * (n + 1) ^ 2) ≤
        (n / 128) * (16 * n ^ 20) :=
      mul_le_mul_of_nonneg_left hDenSq (by positivity)
    _ = n ^ 21 / 8 := by ring
    _ ≤ 2 * n * (n ^ 10 - 1) * (n ^ 2 - 1) ^ 3 *
      (n ^ 2 + 1) ^ 2 := hLowerNum

/-- The equivalent rescaled masses x=1, y=n⁻⁹ have the same normalized
heat rate as x=n⁹, y=1, so the low-moment restriction is genuine. -/
theorem h3_twoBandNearYoung_rescaledRate_eq244
    (n : ℝ) (hn : 2 ≤ n) :
    h3TwoBandVariableHeatRate244 (n ^ 2) 1 (1 / n ^ 9) =
      h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9) 1 := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244,
    h3_twoBandVariableHeat_rate_eq_factor244]
  have hnPos : 0 < n := by linarith only [hn]
  have hn0 : n ≠ 0 := ne_of_gt hnPos
  have hNinth : n ^ 9 ≠ 0 := pow_ne_zero 9 hn0
  have hSum : n ^ 9 + 1 ≠ 0 := by positivity
  have hPlus : n + 1 ≠ 0 := by positivity
  have hTop : n ^ 9 + n ^ 8 ≠ 0 := by positivity
  field_simp [hn0, hNinth, hSum, hPlus, hTop]
  <;> ring

/-- The rescaled and unscaled two-band states have EXACTLY the same
normalized Young gap. The near-saturation condition therefore holds for
the very same bounded-moment state whose heat production is large. -/
theorem h3_twoBandNearYoung_rescaledGap_eq244
    (n : ℝ) (hn : 2 ≤ n) :
    h3TwoBandVariableYoungGap244 (n ^ 2) 1 (1 / n ^ 9) =
      h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9) 1 := by
  have hnPos : 0 < n := by linarith only [hn]
  have hn0 : n ≠ 0 := ne_of_gt hnPos
  have hNinth : n ^ 9 ≠ 0 := pow_ne_zero 9 hn0
  have hSum : n ^ 9 + 1 ≠ 0 := by positivity
  have hTop : n ^ 9 + n ^ 8 ≠ 0 := by positivity
  have hDenLeft : (1 + 1 / n ^ 9) *
      (1 + (n ^ 2) ^ 4 * (1 / n ^ 9)) ≠ 0 := by positivity
  have hDenRight : (n ^ 9 + 1) * (n ^ 9 + (n ^ 2) ^ 4) ≠ 0 := by
    positivity
  unfold h3TwoBandVariableYoungGap244
  field_simp [hn0, hNinth, hSum, hTop, hDenLeft, hDenRight]
  <;> ring

/-- The rescaled fourth, second, and zeroth radial moments all lie in [1,2].
This is the same family for which the normalized Young gap tends to zero. -/
theorem h3_twoBandNearYoung_rescaledLowMoments_bounded244
    (n : ℝ) (hn : 2 ≤ n) :
    1 ≤ (1 : ℝ) + 1 / n ^ 9 ∧
    (1 : ℝ) + 1 / n ^ 9 ≤ 2 ∧
    1 ≤ (1 : ℝ) + 1 / n ^ 5 ∧
    (1 : ℝ) + 1 / n ^ 5 ≤ 2 ∧
    1 ≤ (1 : ℝ) + 1 / n ∧
    (1 : ℝ) + 1 / n ≤ 2 := by
  have hnPos : 0 < n := by linarith only [hn]
  have hn1 : 1 ≤ n := by linarith only [hn]
  have h5 : 1 ≤ n ^ 5 := by
    calc
      (1 : ℝ) = 1 ^ 5 := by norm_num
      _ ≤ n ^ 5 := by gcongr <;> exact hn1
  have h9 : 1 ≤ n ^ 9 := by
    calc
      (1 : ℝ) = 1 ^ 9 := by norm_num
      _ ≤ n ^ 9 := by gcongr <;> exact hn1
  have hInvN : 1 / n ≤ 1 :=
    (div_le_iff₀ hnPos).2 (by linarith only [hn1])
  have hInv5 : 1 / n ^ 5 ≤ 1 :=
    (div_le_iff₀ (pow_pos hnPos 5)).2 (by linarith only [h5])
  have hInv9 : 1 / n ^ 9 ≤ 1 :=
    (div_le_iff₀ (pow_pos hnPos 9)).2 (by linarith only [h9])
  have hNonnegN : 0 ≤ 1 / n := by positivity
  have hNonneg5 : 0 ≤ 1 / n ^ 5 := by positivity
  have hNonneg9 : 0 ≤ 1 / n ^ 9 := by positivity
  constructor
  · linarith only [hNonneg9]
  constructor
  · linarith only [hInv9]
  constructor
  · linarith only [hNonneg5]
  constructor
  · linarith only [hInv5]
  constructor
  · linarith only [hNonnegN]
  · linarith only [hInvN]

/-- Every prescribed near-Young tolerance and heat-rate threshold occur
SIMULTANEOUSLY in one two-band spectral configuration with bounded lower
moments. This is a scalar obstruction; the family is not a NS solution. -/
theorem h3_twoBandNearYoung_boundedMoments_unboundedHeat244 :
    ∀ δ B : ℝ, 0 < δ → ∃ n : ℝ, 2 ≤ n ∧
      h3TwoBandVariableYoungGap244 (n ^ 2) 1 (1 / n ^ 9) ≤ δ ∧
      B < h3TwoBandVariableHeatRate244 (n ^ 2) 1 (1 / n ^ 9) ∧
      1 ≤ (1 : ℝ) + 1 / n ^ 9 ∧
      (1 : ℝ) + 1 / n ^ 9 ≤ 2 ∧
      1 ≤ (1 : ℝ) + 1 / n ^ 5 ∧
      (1 : ℝ) + 1 / n ^ 5 ≤ 2 ∧
      1 ≤ (1 : ℝ) + 1 / n ∧
      (1 : ℝ) + 1 / n ≤ 2 := by
  intro δ B hδ
  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (max (max (1 / δ) (128 * B)) (2 : ℝ))
  have hn2 : 2 ≤ (N : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hnPos : 0 < (N : ℝ) := by linarith only [hn2]
  have hInvBound : 1 / δ < (N : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hRateBound : 128 * B < (N : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hInvSmall : 1 / (N : ℝ) < δ := by
    have hScaled := mul_lt_mul_of_pos_left hInvBound hδ
    have hSimpl : δ * (1 / δ) = 1 := by
      field_simp [ne_of_gt hδ]
    have hOne : 1 < δ * (N : ℝ) := by
      rw [hSimpl] at hScaled
      exact hScaled
    exact (div_lt_iff₀ hnPos).2 (by
      nlinarith only [hOne])
  have hGap := h3_twoBandNearYoung_gap_le_inverse244 (N : ℝ) hn2
  have hRate := h3_twoBandNearYoung_heatRate_ge_linear244 (N : ℝ) hn2
  have hBigRate : B < h3TwoBandVariableHeatRate244
      ((N : ℝ) ^ 2) ((N : ℝ) ^ 9) 1 := by
    linarith only [hRateBound, hRate]
  obtain ⟨hm0, hm0B, hm2, hm2B, hm4, hm4B⟩ :=
    h3_twoBandNearYoung_rescaledLowMoments_bounded244 (N : ℝ) hn2
  refine ⟨(N : ℝ), hn2, ?_, ?_, hm0, hm0B, hm2, hm2B, hm4, hm4B⟩
  · rw [h3_twoBandNearYoung_rescaledGap_eq244 (N : ℝ) hn2]
    exact le_of_lt (lt_of_le_of_lt hGap hInvSmall)
  · rw [h3_twoBandNearYoung_rescaledRate_eq244 (N : ℝ) hn2]
    exact hBigRate

end
end PrimeTensor.FirstMonomialTriad
