import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdGlobalHeatBarycenterSign244
import Mathlib.Tactic

/-!
# Arbitrarily large positive heat concentration from two separated radial bands

For two algebraic Fourier bands at q=1 and q=r, with positive masses x,y,
all six moments are m_k=x+r^k y.  The EXACT signed heat numerator is

  2 (x+r²y) xy (r-1)^3 (r+1)^2 (x-r²y).

Thus the threshold for heat concentration is x=r²y, and the frequency
gap matters.  In particular x=r⁴,y=1 gives a dimensionless normalized
heat production growing at least linearly in r for r≥2:

  B_heat(r,r⁴,1) ≥ r/128.

The same two-band states may be rescaled to masses x=1,y=r⁻⁴, for which
m0 and m2 lie in [1,2], and m4=2.  Therefore low-moment bounds alone do
not provide a universal normalized heat-production ceiling.  This is a
SCALAR SPECTRAL TEST, not a construction of Navier–Stokes solutions or an
anti-concentration theorem.  The actual PDE heat-rate factorization was
proved in GlobalHeatBarycenterSign244.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

/-- Algebraic two-band normalized physical HEAT source at frequency
weights 1 and r, with respective scalar spectral masses x and y. -/
noncomputable def h3TwoBandVariableHeatRate244 (r x y : ℝ) : ℝ :=
  (2 * (x + r ^ 2 * y) *
    h3GlobalRadialHeatBarycenterImbalance244
      (x + y) (x + r * y) (x + r ^ 2 * y)
      (x + r ^ 3 * y) (x + r ^ 4 * y) (x + r ^ 5 * y)) /
    ((x + y) * (x + r ^ 4 * y)) ^ 2

/-- Exact six-moment imbalance for arbitrary second-band radial weight r.
The r=2 theorem in the previous module is a specialization. -/
theorem h3_twoBandVariableHeat_imbalance_factor244 (r x y : ℝ) :
    h3GlobalRadialHeatBarycenterImbalance244
      (x + y) (x + r * y) (x + r ^ 2 * y)
      (x + r ^ 3 * y) (x + r ^ 4 * y) (x + r ^ 5 * y) =
    x * y * (r - 1) ^ 3 * (r + 1) ^ 2 * (x - r ^ 2 * y) := by
  unfold h3GlobalRadialHeatBarycenterImbalance244
  ring

/-- No absolute value is taken: this is the exact sign factorization. -/
theorem h3_twoBandVariableHeat_rate_eq_factor244 (r x y : ℝ) :
    h3TwoBandVariableHeatRate244 r x y =
      (2 * (x + r ^ 2 * y) *
        (x * y * (r - 1) ^ 3 * (r + 1) ^ 2 * (x - r ^ 2 * y))) /
        ((x + y) * (x + r ^ 4 * y)) ^ 2 := by
  unfold h3TwoBandVariableHeatRate244
  rw [h3_twoBandVariableHeat_imbalance_factor244]

/-- For a higher second frequency r>1, positive heat concentration is
possible exactly on the mass-dominated side x>r²y. -/
theorem h3_twoBandVariableHeat_positive_of_massDominance244
    (r x y : ℝ) (hr : 1 < r) (hx : 0 < x) (hy : 0 < y)
    (hDom : r ^ 2 * y < x) :
    0 < h3TwoBandVariableHeatRate244 r x y := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244]
  have hGap : 0 < r - 1 := by linarith only [hr]
  have hHigh : 0 < x - r ^ 2 * y := sub_pos.mpr hDom
  apply div_pos
  · positivity
  · positivity

/-- The opposite mass allocation produces strictly negative heat
concentration, although all six moment masses are nonnegative. -/
theorem h3_twoBandVariableHeat_negative_of_massDeficit244
    (r x y : ℝ) (hr : 1 < r) (hx : 0 < x) (hy : 0 < y)
    (hDom : x < r ^ 2 * y) :
    h3TwoBandVariableHeatRate244 r x y < 0 := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244]
  have hGap : 0 < r - 1 := by linarith only [hr]
  have hLow : x - r ^ 2 * y < 0 := sub_neg.mpr hDom
  have hPrefactor :
      0 < 2 * (x + r ^ 2 * y) *
        (x * y * (r - 1) ^ 3 * (r + 1) ^ 2) := by
    positivity
  have hNum :
      2 * (x + r ^ 2 * y) *
        (x * y * (r - 1) ^ 3 * (r + 1) ^ 2 * (x - r ^ 2 * y)) < 0 := by
    calc
      2 * (x + r ^ 2 * y) *
          (x * y * (r - 1) ^ 3 * (r + 1) ^ 2 * (x - r ^ 2 * y)) =
        (2 * (x + r ^ 2 * y) *
          (x * y * (r - 1) ^ 3 * (r + 1) ^ 2)) *
          (x - r ^ 2 * y) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hPrefactor hLow
  exact div_neg_of_neg_of_pos hNum (by positivity)

/-- Rescaled high-frequency family, presented without inverse powers in
the actual rate: x=r⁴, y=1. It has a positive rate that grows as r/2. -/
theorem h3_twoBandHighFrequency_rate_eq_closed244
    (r : ℝ) (hr : 2 ≤ r) :
    h3TwoBandVariableHeatRate244 r (r ^ 4) 1 =
      ((r - 1) ^ 4 * (r + 1) ^ 3 * (r ^ 2 + 1)) /
        (2 * (r ^ 4 + 1) ^ 2) := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244]
  have hr0 : r ≠ 0 := ne_of_gt (by linarith only [hr] : 0 < r)
  have hSum : r ^ 4 + 1 ≠ 0 := by positivity
  field_simp [hr0, hSum]
  <;> ring

/-- Quantitative lower bound, without unproved nonlinear assumptions.
This prevents a uniform positive heat ceiling even in the two-band class. -/
theorem h3_twoBandHighFrequency_rate_ge_linear244
    (r : ℝ) (hr : 2 ≤ r) :
    r / 128 ≤ h3TwoBandVariableHeatRate244 r (r ^ 4) 1 := by
  rw [h3_twoBandHighFrequency_rate_eq_closed244 r hr]
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hr1 : 1 ≤ r := by linarith only [hr]
  have hHalf : r / 2 ≤ r - 1 := by linarith only [hr]
  have hPlus : r ≤ r + 1 := by linarith
  have hSquare : r ^ 2 ≤ r ^ 2 + 1 := by linarith
  have hFourth : 1 ≤ r ^ 4 := by
    have hp : (1 : ℝ) ^ 4 ≤ r ^ 4 := by
      gcongr <;> exact hr1
    simpa only [one_pow] using hp
  have hPowHalf : (r / 2) ^ 4 ≤ (r - 1) ^ 4 := by
    gcongr <;> linarith only [hHalf, hr]
  have hPowPlus : r ^ 3 ≤ (r + 1) ^ 3 := by
    gcongr <;> linarith only [hPlus, hr]
  have hAB : (r / 2) ^ 4 * r ^ 3 ≤
      (r - 1) ^ 4 * (r + 1) ^ 3 := by
    calc
      (r / 2) ^ 4 * r ^ 3 ≤ (r - 1) ^ 4 * r ^ 3 :=
        mul_le_mul_of_nonneg_right hPowHalf (by positivity)
      _ ≤ (r - 1) ^ 4 * (r + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hPowPlus (by positivity)
  have hLower : r ^ 9 / 16 ≤
      (r - 1) ^ 4 * (r + 1) ^ 3 * (r ^ 2 + 1) := by
    calc
      r ^ 9 / 16 = (r / 2) ^ 4 * r ^ 3 * r ^ 2 := by ring
      _ ≤ (r - 1) ^ 4 * (r + 1) ^ 3 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hAB (by positivity)
      _ ≤ (r - 1) ^ 4 * (r + 1) ^ 3 * (r ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hSquare (by positivity)
  have hBase : r ^ 4 + 1 ≤ 2 * r ^ 4 := by
    linarith only [hFourth]
  have hDenSquare : (r ^ 4 + 1) ^ 2 ≤ (2 * r ^ 4) ^ 2 := by
    gcongr <;> linarith only [hBase, hFourth]
  have hDenBound : 2 * (r ^ 4 + 1) ^ 2 ≤ 8 * r ^ 8 := by
    calc
      2 * (r ^ 4 + 1) ^ 2 ≤ 2 * (2 * r ^ 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hDenSquare (by norm_num)
      _ = 8 * r ^ 8 := by ring
  have hScale : (r / 128) * (2 * (r ^ 4 + 1) ^ 2) ≤
      r ^ 9 / 16 := by
    calc
      (r / 128) * (2 * (r ^ 4 + 1) ^ 2) ≤
          (r / 128) * (8 * r ^ 8) :=
        mul_le_mul_of_nonneg_left hDenBound (by positivity)
      _ = r ^ 9 / 16 := by ring
  exact (le_div_iff₀ (by positivity : 0 < 2 * (r ^ 4 + 1) ^ 2)).2
    (hScale.trans hLower)

/-- The rescaled two-band family with masses 1 and r⁻⁴ has uniformly
bounded zeroth, second, and fourth moments when r≥2. -/
theorem h3_twoBandHighFrequency_rescaledLowMoments_bounded244
    (r : ℝ) (hr : 2 ≤ r) :
    1 ≤ (1 : ℝ) + 1 / r ^ 4 ∧
    (1 : ℝ) + 1 / r ^ 4 ≤ 2 ∧
    1 ≤ (1 : ℝ) + 1 / r ^ 2 ∧
    (1 : ℝ) + 1 / r ^ 2 ≤ 2 ∧
    (1 : ℝ) + r ^ 4 / r ^ 4 = 2 := by
  have hrpos : 0 < r := by linarith only [hr]
  have hr1 : 1 ≤ r := by linarith only [hr]
  have hPow2 : 1 ≤ r ^ 2 := by
    have hp : (1 : ℝ) ^ 2 ≤ r ^ 2 := by
      gcongr <;> exact hr1
    simpa only [one_pow] using hp
  have hPow4 : 1 ≤ r ^ 4 := by
    have hp : (1 : ℝ) ^ 4 ≤ r ^ 4 := by
      gcongr <;> exact hr1
    simpa only [one_pow] using hp
  have hi2 : 1 / r ^ 2 ≤ 1 :=
    (div_le_iff₀ (pow_pos hrpos 2)).2 (by linarith only [hPow2])
  have hi4 : 1 / r ^ 4 ≤ 1 :=
    (div_le_iff₀ (pow_pos hrpos 4)).2 (by linarith only [hPow4])
  have hNonneg2 : 0 ≤ 1 / r ^ 2 := by positivity
  have hNonneg4 : 0 ≤ 1 / r ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hNonneg4]
  · linarith only [hi4]
  · linarith only [hNonneg2]
  · linarith only [hi2]
  · field_simp [ne_of_gt hrpos] <;> ring

/-- The rescaled masses x=1, y=r⁻⁴ have exactly the same normalized
heat rate as the unscaled masses x=r⁴, y=1.  This makes the bounded-low-
moment / unbounded-rate comparison an exact algebraic counterexample. -/
theorem h3_twoBandHighFrequency_rescaledRate_eq_unscaled244
    (r : ℝ) (hr : 2 ≤ r) :
    h3TwoBandVariableHeatRate244 r 1 (1 / r ^ 4) =
      h3TwoBandVariableHeatRate244 r (r ^ 4) 1 := by
  rw [h3_twoBandVariableHeat_rate_eq_factor244,
    h3_twoBandVariableHeat_rate_eq_factor244]
  have hrpos : 0 < r := by linarith only [hr]
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hFourth : r ^ 4 ≠ 0 := pow_ne_zero 4 hr0
  have hSum : r ^ 4 + 1 ≠ 0 := by positivity
  field_simp [hr0, hFourth, hSum]
  <;> ring

/-- For every proposed scalar bound there is a separated-frequency two-band
model whose normalized pure heat concentration exceeds it. -/
theorem h3_twoBandHighFrequency_heatRate_unboundedAbove244 :
    ∀ B : ℝ, ∃ r : ℝ, 2 ≤ r ∧
      B < h3TwoBandVariableHeatRate244 r (r ^ 4) 1 := by
  intro B
  obtain ⟨n, hn⟩ := exists_nat_gt (max (128 * B) (2 : ℝ))
  have hR : 2 ≤ (n : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
  have hB : 128 * B < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hn
  refine ⟨(n : ℝ), hR, ?_⟩
  have hLower := h3_twoBandHighFrequency_rate_ge_linear244 (n : ℝ) hR
  linarith only [hB, hLower]

/-- The heat concentration rate has no numerical ceiling even in a
two-band class with all three lower spectral moments uniformly bounded.
This is an algebraic obstruction, not a physical Navier–Stokes trajectory. -/
theorem h3_twoBandHighFrequency_boundedMoments_unboundedHeat244 :
    ∀ B : ℝ, ∃ r : ℝ, 2 ≤ r ∧
      1 ≤ (1 : ℝ) + 1 / r ^ 4 ∧
      (1 : ℝ) + 1 / r ^ 4 ≤ 2 ∧
      1 ≤ (1 : ℝ) + 1 / r ^ 2 ∧
      (1 : ℝ) + 1 / r ^ 2 ≤ 2 ∧
      (1 : ℝ) + r ^ 4 / r ^ 4 = 2 ∧
      B < h3TwoBandVariableHeatRate244 r 1 (1 / r ^ 4) := by
  intro B
  obtain ⟨r, hr, hRate⟩ := h3_twoBandHighFrequency_heatRate_unboundedAbove244 B
  obtain ⟨hm0, hm0B, hm2, hm2B, hm4⟩ :=
    h3_twoBandHighFrequency_rescaledLowMoments_bounded244 r hr
  refine ⟨r, hr, hm0, hm0B, hm2, hm2B, hm4, ?_⟩
  rw [h3_twoBandHighFrequency_rescaledRate_eq_unscaled244 r hr]
  exact hRate

end
end PrimeTensor.FirstMonomialTriad
