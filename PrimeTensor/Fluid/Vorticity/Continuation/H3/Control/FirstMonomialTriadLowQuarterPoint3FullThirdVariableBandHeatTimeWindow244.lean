import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3FullThirdVariableBandNearYoungHeatEscape244
import Mathlib.Tactic

/-!
# Temporal exhaustion of a large instantaneous two-band heat rate

The near-Young two-band family has radial frequencies q=1,n², masses
x=n⁹,y=1 and initial heat concentration rate at least n/128, while
its normalized Young gap is at most 1/n. Here we evolve the two masses
under the LINEAR heat equation. After removing the common e^(-2t)
factor, the relative high-band mass is

  y(t) = exp(-2 (n²-1) t).

The gap is nonnegative and nonincreasing for t≥0; therefore its TOTAL
possible decrease over any later time is at most 1/n. This explicitly
separates unbounded instantaneous concentration rate from small total
concentration change. It is an algebraic two-band heat model, not a
Navier–Stokes solution or a nonlinear regularity theorem.
-/

namespace PrimeTensor.FirstMonomialTriad

open PrimeTensor.Bridge.Euclidean MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section
set_option maxHeartbeats 1800000

/-- Exact cross-multiplied difference of the normalized two-band gaps.
This is a useful monotonicity identity: the factor x²-r⁴yz fixes the sign. -/
theorem h3_twoBandYoungGap_highMass_difference244
    (r x y z : ℝ) (hr : 0 ≤ r) (hx : 0 < x)
    (hy : 0 < y) (hz : 0 < z) :
    h3TwoBandVariableYoungGap244 r x z -
        h3TwoBandVariableYoungGap244 r x y =
      (x * (r ^ 2 - 1) ^ 2 * (z - y) *
        (x ^ 2 - r ^ 4 * y * z)) /
      ((x + y) * (x + r ^ 4 * y) *
        ((x + z) * (x + r ^ 4 * z))) := by
  rw [h3_twoBandVariableYoungGap_eq_variance244 r x z hx hz hr,
    h3_twoBandVariableYoungGap_eq_variance244 r x y hx hy hr]
  have hXy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hXz : x + z ≠ 0 := ne_of_gt (add_pos hx hz)
  have hRy : x + r ^ 4 * y ≠ 0 := by positivity
  have hRz : x + r ^ 4 * z ≠ 0 := by positivity
  field_simp [hXy, hXz, hRy, hRz]
  <;> ring

/-- Along a positive high-mass attenuation, the two-band gap decreases
provided the geometric mean of the high masses stays below x/r². -/
theorem h3_twoBandYoungGap_mono_highMass244
    (r x y z : ℝ) (hr : 0 ≤ r) (hx : 0 < x)
    (hy : 0 < y) (hyz : y ≤ z)
    (hBalance : r ^ 4 * y * z ≤ x ^ 2) :
    h3TwoBandVariableYoungGap244 r x y ≤
      h3TwoBandVariableYoungGap244 r x z := by
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hDiff := h3_twoBandYoungGap_highMass_difference244
    r x y z hr hx hy hz
  have hPos : 0 ≤
      h3TwoBandVariableYoungGap244 r x z -
        h3TwoBandVariableYoungGap244 r x y := by
    rw [hDiff]
    have hYZ : 0 ≤ z - y := sub_nonneg.mpr hyz
    have hRest : 0 ≤ x ^ 2 - r ^ 4 * y * z :=
      sub_nonneg.mpr hBalance
    positivity
  linarith only [hPos]

/-- Heat attenuation of the relative high-band squared velocity mass.
The common low-frequency heat factor cancels in the normalized gap. -/
noncomputable def h3TwoBandNearYoungHeatRelativeHighMass244
    (n t : ℝ) : ℝ :=
  Real.exp ((-2 : ℝ) * (n ^ 2 - 1) * t)

/-- The algebraic normalized Young gap of the EXACT two-band heat orbit
with initial mass ratio n⁹:1. -/
noncomputable def h3TwoBandNearYoungHeatGapAt244
    (n t : ℝ) : ℝ :=
  h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9)
    (h3TwoBandNearYoungHeatRelativeHighMass244 n t)

/-- The relative high-band mass is positive and at most one at all
nonnegative elapsed times. -/
theorem h3_twoBandNearYoungHeat_relativeMass_pos_le_one244
    (n t : ℝ) (hn : 2 ≤ n) (ht : 0 ≤ t) :
    0 < h3TwoBandNearYoungHeatRelativeHighMass244 n t ∧
      h3TwoBandNearYoungHeatRelativeHighMass244 n t ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by linarith only [hn]
  have hn2 : (1 : ℝ) ≤ n ^ 2 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
      _ ≤ n ^ 2 := by gcongr <;> exact hn1
  have hCoeff : (-2 : ℝ) * (n ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (sub_nonneg.mpr hn2)
  have hArg : (-2 : ℝ) * (n ^ 2 - 1) * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hCoeff ht
  constructor
  · exact Real.exp_pos _
  · change Real.exp ((-2 : ℝ) * (n ^ 2 - 1) * t) ≤ 1
    have hExp : Real.exp ((-2 : ℝ) * (n ^ 2 - 1) * t) ≤
        Real.exp 0 := Real.exp_le_exp.mpr hArg
    simpa only [Real.exp_zero] using hExp

/-- Relative high-band heat mass is antitone as elapsed time increases. -/
theorem h3_twoBandNearYoungHeat_relativeMass_antitone244
    (n s t : ℝ) (hn : 2 ≤ n) (hst : s ≤ t) :
    h3TwoBandNearYoungHeatRelativeHighMass244 n t ≤
      h3TwoBandNearYoungHeatRelativeHighMass244 n s := by
  have hn1 : (1 : ℝ) ≤ n := by linarith only [hn]
  have hn2 : (1 : ℝ) ≤ n ^ 2 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
      _ ≤ n ^ 2 := by gcongr <;> exact hn1
  have hCoeff : (-2 : ℝ) * (n ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (sub_nonneg.mpr hn2)
  have hArg := mul_le_mul_of_nonpos_left hst hCoeff
  change Real.exp ((-2 : ℝ) * (n ^ 2 - 1) * t) ≤
    Real.exp ((-2 : ℝ) * (n ^ 2 - 1) * s)
  exact Real.exp_le_exp.mpr hArg

/-- For n≥2, the dominating low-band mass n⁹ defeats the fourth power
of the spectral gap even if both relative high masses are as large as 1. -/
theorem h3_twoBandNearYoungHeat_highMass_balance244
    (n y z : ℝ) (hn : 2 ≤ n)
    (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (n ^ 2) ^ 4 * y * z ≤ (n ^ 9) ^ 2 := by
  have hn0 : 0 ≤ n := by linarith only [hn]
  have hn1 : (1 : ℝ) ≤ n := by linarith only [hn]
  have hPow10 : (1 : ℝ) ≤ n ^ 10 := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ 10 := by norm_num
      _ ≤ n ^ 10 := by gcongr <;> exact hn1
  have hPow : n ^ 8 ≤ n ^ 18 := by
    calc
      n ^ 8 = n ^ 8 * 1 := by ring
      _ ≤ n ^ 8 * n ^ 10 :=
        mul_le_mul_of_nonneg_left hPow10 (pow_nonneg hn0 8)
      _ = n ^ 18 := by ring
  calc
    (n ^ 2) ^ 4 * y * z = n ^ 8 * (y * z) := by ring
    _ ≤ n ^ 8 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hn0 8)
      calc
        y * z ≤ 1 * z := mul_le_mul_of_nonneg_right hy1 hz
        _ = z := by ring
        _ ≤ 1 := hz1
    _ = n ^ 8 := by ring
    _ ≤ n ^ 18 := hPow
    _ = (n ^ 9) ^ 2 := by ring

/-- The normalized Young gap is antitone along the actual two-band HEAT
orbit. This uses high-mass attenuation, not a Navier-Stokes sign claim. -/
theorem h3_twoBandNearYoungHeat_gap_antitone244
    (n s t : ℝ) (hn : 2 ≤ n) (hs : 0 ≤ s) (hst : s ≤ t) :
    h3TwoBandNearYoungHeatGapAt244 n t ≤
      h3TwoBandNearYoungHeatGapAt244 n s := by
  have ht : 0 ≤ t := le_trans hs hst
  obtain ⟨hy, hy1⟩ :=
    h3_twoBandNearYoungHeat_relativeMass_pos_le_one244 n t hn ht
  obtain ⟨hz, hz1⟩ :=
    h3_twoBandNearYoungHeat_relativeMass_pos_le_one244 n s hn hs
  have hyz := h3_twoBandNearYoungHeat_relativeMass_antitone244
    n s t hn hst
  have hBalance := h3_twoBandNearYoungHeat_highMass_balance244
    n (h3TwoBandNearYoungHeatRelativeHighMass244 n t)
      (h3TwoBandNearYoungHeatRelativeHighMass244 n s)
      hn hy.le hy1 hz.le hz1
  unfold h3TwoBandNearYoungHeatGapAt244
  exact h3_twoBandYoungGap_mono_highMass244 _ _ _ _
    (by positivity) (by positivity) hy hyz hBalance

/-- At t=0 the new heat-orbit gap agrees definitionally with the
previously formalized near-Young spectral configuration. -/
theorem h3_twoBandNearYoungHeat_gap_initial244 (n : ℝ) :
    h3TwoBandNearYoungHeatGapAt244 n 0 =
      h3TwoBandVariableYoungGap244 (n ^ 2) (n ^ 9) 1 := by
  simp [h3TwoBandNearYoungHeatGapAt244,
    h3TwoBandNearYoungHeatRelativeHighMass244]

/-- At every nonnegative elapsed time, the heat gap remains nonnegative.
This property is independent of the heat-barycenter sign. -/
theorem h3_twoBandNearYoungHeat_gap_nonneg244
    (n t : ℝ) (hn : 2 ≤ n) (_ht : 0 ≤ t) :
    0 ≤ h3TwoBandNearYoungHeatGapAt244 n t := by
  have hnPos : 0 < n := by linarith only [hn]
  have hyPos :
      0 < h3TwoBandNearYoungHeatRelativeHighMass244 n t := by
    unfold h3TwoBandNearYoungHeatRelativeHighMass244
    exact Real.exp_pos _
  have hrNonneg : 0 ≤ n ^ 2 := pow_nonneg hnPos.le 2
  unfold h3TwoBandNearYoungHeatGapAt244
  rw [h3_twoBandVariableYoungGap_eq_variance244
    (n ^ 2) (n ^ 9)
    (h3TwoBandNearYoungHeatRelativeHighMass244 n t)
    (pow_pos hnPos 9) hyPos hrNonneg]
  have hxNonneg : 0 ≤ n ^ 9 := pow_nonneg hnPos.le 9
  have hrFourthNonneg : 0 ≤ (n ^ 2) ^ 4 := pow_nonneg hrNonneg 4
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg hxNonneg hyPos.le) (sq_nonneg _)
  · exact mul_nonneg
      (add_nonneg hxNonneg hyPos.le)
      (add_nonneg hxNonneg (mul_nonneg hrFourthNonneg hyPos.le))

/-- The heat flow cannot reduce normalized spectral variance by more
than the entire small initial gap, regardless of its large initial rate. -/
theorem h3_twoBandNearYoungHeat_totalGapDrop_le_inverse244
    (n t : ℝ) (hn : 2 ≤ n) (ht : 0 ≤ t) :
    0 ≤ h3TwoBandNearYoungHeatGapAt244 n 0 -
        h3TwoBandNearYoungHeatGapAt244 n t ∧
      h3TwoBandNearYoungHeatGapAt244 n 0 -
        h3TwoBandNearYoungHeatGapAt244 n t ≤ 1 / n := by
  have hMono := h3_twoBandNearYoungHeat_gap_antitone244
    n 0 t hn le_rfl ht
  have hNonneg := h3_twoBandNearYoungHeat_gap_nonneg244 n t hn ht
  have hInitial := h3_twoBandNearYoungHeat_gap_initial244 n
  have hBound := h3_twoBandNearYoung_gap_le_inverse244 n hn
  rw [← hInitial] at hBound
  constructor
  · linarith only [hMono]
  · linarith only [hNonneg, hBound]

/-- Quantitative pointwise-versus-temporal separation: instantaneous
heat concentration grows at least linearly with n, but its entire
nonnegative-time variance change is at most 1/n. -/
theorem h3_twoBandNearYoungHeat_largeRate_smallTotalChange244
    (n : ℝ) (hn : 2 ≤ n) :
    n / 128 ≤ h3TwoBandVariableHeatRate244 (n ^ 2) (n ^ 9) 1 ∧
    ∀ t : ℝ, 0 ≤ t →
      0 ≤ h3TwoBandNearYoungHeatGapAt244 n 0 -
        h3TwoBandNearYoungHeatGapAt244 n t ∧
      h3TwoBandNearYoungHeatGapAt244 n 0 -
        h3TwoBandNearYoungHeatGapAt244 n t ≤ 1 / n := by
  exact ⟨h3_twoBandNearYoung_heatRate_ge_linear244 n hn,
    fun t ht => h3_twoBandNearYoungHeat_totalGapDrop_le_inverse244 n t hn ht⟩

end
end PrimeTensor.FirstMonomialTriad
