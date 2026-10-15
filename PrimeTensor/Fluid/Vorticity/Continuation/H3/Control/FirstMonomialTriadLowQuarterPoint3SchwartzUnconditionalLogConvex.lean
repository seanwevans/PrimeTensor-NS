import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentJointCauchy

/-!
# Unconditional real-Schwartz cubic H3 interpolation at finite axis constant

The previous module has *proved* for every actual real Schwartz velocity:

  E1^2 <= n E0 E2,      E2^2 <= n E1 E3,

where n is the number of spatial axes, equal to three in `Depth.three`.
This module eliminates E1/E2 by division-free algebra, obtaining

  E1^3 <= n^3 E0^2 E3,  E2^3 <= n^3 E0 E3^2.

At a balanced positive spatial scale (scale^6 E3 = E0), the complete
unnormalized scaled energy polynomial is then bounded by (2+2n)E0.
Unlike the preceding conditional bridge, these estimates no longer assume
Schwartz Fourier log-convexity; they follow directly from proved slotwise
Schwartz Cauchy estimates. The factor n remains and is NOT sharp.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeUnconditionalLogConvex (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Two adjacent Cauchy inequalities with a common finite-dimensional loss
`K` imply both endpoint cubic bounds with loss `K^3`. This uses no divisions,
including at zero intermediate energies. -/
theorem criticalHalf_relaxedAdjacentCauchy_implies_cubicLogConvex
    (K E0 E1 E2 E3 : ℝ)
    (hK : 0 ≤ K) (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (h01 : E1 ^ 2 ≤ K * E0 * E2)
    (h12 : E2 ^ 2 ≤ K * E1 * E3) :
    E1 ^ 3 ≤ K ^ 3 * E0 ^ 2 * E3 ∧
      E2 ^ 3 ≤ K ^ 3 * E0 * E3 ^ 2 := by
  have hFirstFourth : E1 ^ 4 ≤ K ^ 3 * E0 ^ 2 * E3 * E1 := by
    calc
      E1 ^ 4 = (E1 ^ 2) ^ 2 := by ring
      _ ≤ (K * E0 * E2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h01 2
      _ = (K * E0) ^ 2 * E2 ^ 2 := by ring
      _ ≤ (K * E0) ^ 2 * (K * E1 * E3) :=
        mul_le_mul_of_nonneg_left h12 (sq_nonneg _)
      _ = K ^ 3 * E0 ^ 2 * E3 * E1 := by ring
  have hSecondFourth : E2 ^ 4 ≤ (K ^ 3 * E0 * E3 ^ 2) * E2 := by
    calc
      E2 ^ 4 = (E2 ^ 2) ^ 2 := by ring
      _ ≤ (K * E1 * E3) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h12 2
      _ = (K * E3) ^ 2 * E1 ^ 2 := by ring
      _ ≤ (K * E3) ^ 2 * (K * E0 * E2) :=
        mul_le_mul_of_nonneg_left h01 (sq_nonneg _)
      _ = (K ^ 3 * E0 * E3 ^ 2) * E2 := by ring
  constructor
  · by_cases hz : E1 = 0
    · subst E1
      simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
      positivity
    · have hp : 0 < E1 := lt_of_le_of_ne hE1 (Ne.symm hz)
      apply (mul_le_mul_iff_of_pos_right hp).mp
      calc
        E1 ^ 3 * E1 = E1 ^ 4 := by ring
        _ ≤ K ^ 3 * E0 ^ 2 * E3 * E1 := hFirstFourth
  · by_cases hz : E2 = 0
    · subst E2
      simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
      positivity
    · have hp : 0 < E2 := lt_of_le_of_ne hE2 (Ne.symm hz)
      apply (mul_le_mul_iff_of_pos_right hp).mp
      calc
        E2 ^ 3 * E2 = E2 ^ 4 := by ring
        _ ≤ (K ^ 3 * E0 * E3 ^ 2) * E2 := hSecondFourth

/-- Cubic interpolation for the *actual* complete physical 3D Schwartz
energy blocks; no interpolation hypotheses and no spectral/PDE conditions. -/
theorem lowNormalRealSchwartzH3Energy_unconditional_cubicLogConvex
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 3 ≤
        (Fintype.card A3 : ℝ) ^ 3 *
          (lowNormalRealSchwartzH3Energy0 f) ^ 2 *
          lowNormalRealSchwartzH3Energy3 f
      ∧
    (lowNormalRealSchwartzH3Energy2 f) ^ 3 ≤
        (Fintype.card A3 : ℝ) ^ 3 *
          lowNormalRealSchwartzH3Energy0 f *
          (lowNormalRealSchwartzH3Energy3 f) ^ 2 := by
  exact criticalHalf_relaxedAdjacentCauchy_implies_cubicLogConvex
    (Fintype.card A3 : ℝ)
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (Nat.cast_nonneg _)
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    (lowNormalRealSchwartzH3Energy1_sq_le_axisCard_mul_E0_E2 f)
    (lowNormalRealSchwartzH3Energy2_sq_le_axisCard_mul_E1_E3 f)

/-- A relaxed cubic interpolation inequality bounds each intermediate
term at any scale balancing the order-zero and order-three energies. -/
theorem criticalHalf_relaxedLogConvex_balancedScale_energyUpper
    (K E0 E1 E2 E3 scale : ℝ)
    (hK : 0 ≤ K) (hE0 : 0 < E0) (hscale : 0 < scale)
    (hOne : E1 ^ 3 ≤ K ^ 3 * E0 ^ 2 * E3)
    (hTwo : E2 ^ 3 ≤ K ^ 3 * E0 * E3 ^ 2)
    (hBalance : scale ^ 6 * E3 = E0) :
    E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 ≤
      (2 + 2 * K) * E0 := by
  have hOneCube : (scale ^ 2 * E1) ^ 3 ≤ (K * E0) ^ 3 := by
    calc
      (scale ^ 2 * E1) ^ 3 = scale ^ 6 * E1 ^ 3 := by ring
      _ ≤ scale ^ 6 * (K ^ 3 * E0 ^ 2 * E3) :=
        mul_le_mul_of_nonneg_left hOne (pow_nonneg hscale.le 6)
      _ = K ^ 3 * E0 ^ 2 * (scale ^ 6 * E3) := by ring
      _ = (K * E0) ^ 3 := by rw [hBalance]; ring
  have hTwoCube : (scale ^ 4 * E2) ^ 3 ≤ (K * E0) ^ 3 := by
    calc
      (scale ^ 4 * E2) ^ 3 = scale ^ 12 * E2 ^ 3 := by ring
      _ ≤ scale ^ 12 * (K ^ 3 * E0 * E3 ^ 2) :=
        mul_le_mul_of_nonneg_left hTwo (pow_nonneg hscale.le 12)
      _ = K ^ 3 * E0 * (scale ^ 6 * E3) ^ 2 := by ring
      _ = (K * E0) ^ 3 := by rw [hBalance]; ring
  have hK0 : 0 ≤ K * E0 := mul_nonneg hK hE0.le
  have hOneBound : scale ^ 2 * E1 ≤ K * E0 := by
    by_contra hn
    have hlt : K * E0 < scale ^ 2 * E1 := lt_of_not_ge hn
    have hp := pow_lt_pow_left₀ hlt hK0
      (by norm_num : (3 : ℕ) ≠ 0)
    exact (not_lt_of_ge hOneCube) hp
  have hTwoBound : scale ^ 4 * E2 ≤ K * E0 := by
    by_contra hn
    have hlt : K * E0 < scale ^ 4 * E2 := lt_of_not_ge hn
    have hp := pow_lt_pow_left₀ hlt hK0
      (by norm_num : (3 : ℕ) ≠ 0)
    exact (not_lt_of_ge hTwoCube) hp
  rw [hBalance]
  nlinarith only [hOneBound, hTwoBound]

/-- Unconditional full Schwartz four-block energy upper bound at any
positive balancing scale. No separately assumed log-convexity is used. -/
theorem lowNormalRealSchwartzH3Energy_unconditional_balancedScale_upper
    (f : A3 → SchwartzMap V3 ℝ)
    (scale : ℝ) (hscale : 0 < scale)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f) :
    lowNormalRealSchwartzH3Energy0 f +
        scale ^ 2 * lowNormalRealSchwartzH3Energy1 f +
        scale ^ 4 * lowNormalRealSchwartzH3Energy2 f +
        scale ^ 6 * lowNormalRealSchwartzH3Energy3 f ≤
      (2 + 2 * (Fintype.card A3 : ℝ)) *
        lowNormalRealSchwartzH3Energy0 f := by
  obtain ⟨hOne, hTwo⟩ :=
    lowNormalRealSchwartzH3Energy_unconditional_cubicLogConvex f
  exact criticalHalf_relaxedLogConvex_balancedScale_energyUpper
    (Fintype.card A3 : ℝ)
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    scale (Nat.cast_nonneg _) hE0 hscale hOne hTwo hBalance

end
end PrimeTensor.FirstMonomialTriad
