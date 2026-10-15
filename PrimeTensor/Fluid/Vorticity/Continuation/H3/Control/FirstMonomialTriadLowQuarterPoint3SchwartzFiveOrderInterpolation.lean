import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzFourthCoercivity

/-!
# Sharp five-order interpolation for actual physical Schwartz energies

The proved coefficient-one adjacent estimates E1^2 <= E0*E2,
E2^2 <= E1*E3, and E3^2 <= E2*D imply the exact quartic moment
interpolation across derivative orders zero through four:

  E1^4 <= E0^3*D,     E2^2 <= E0*D,     E3^4 <= E0*D^3.

A scalar, division-free proof isolates the only cancellation step and
handles E2=0 separately. The physical corollary uses the actual complete
Schwartz derivative sums at orders zero through four, with no Fourier
identification, solenoidal assumption, auxiliary interpolant or selected slot.

This does not assert that the signed 243-slot nonlinear monomial has a
uniform critical-half bound. It supplies additional exact energy control
for that separate analytic problem.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeFiveOrder (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Three exact adjacent Cauchy bounds imply all endpoint-to-interior
fourth-order interpolation estimates, without any division by an energy.
The sole strictly positive cancellation is handled after a zero case split. -/
theorem criticalHalf_fiveOrder_adjacentCauchy_implies_quartic
    (E0 E1 E2 E3 D : ℝ)
    (h0 : 0 ≤ E0) (h2 : 0 ≤ E2) (hD : 0 ≤ D)
    (h01 : E1 ^ 2 ≤ E0 * E2)
    (h12 : E2 ^ 2 ≤ E1 * E3)
    (h23 : E3 ^ 2 ≤ E2 * D) :
    E1 ^ 4 ≤ E0 ^ 3 * D ∧
      E2 ^ 2 ≤ E0 * D ∧
        E3 ^ 4 ≤ E0 * D ^ 3 := by
  have hFourth : E2 ^ 4 ≤ (E0 * D) * E2 ^ 2 := by
    calc
      E2 ^ 4 = (E2 ^ 2) ^ 2 := by ring
      _ ≤ (E1 * E3) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg E2) h12 2
      _ = E1 ^ 2 * E3 ^ 2 := by ring
      _ ≤ (E0 * E2) * E3 ^ 2 :=
        mul_le_mul_of_nonneg_right h01 (sq_nonneg E3)
      _ ≤ (E0 * E2) * (E2 * D) :=
        mul_le_mul_of_nonneg_left h23 (mul_nonneg h0 h2)
      _ = (E0 * D) * E2 ^ 2 := by ring
  have hMiddle : E2 ^ 2 ≤ E0 * D := by
    by_cases hz : E2 = 0
    · simpa [hz] using mul_nonneg h0 hD
    · have hp : 0 < E2 := lt_of_le_of_ne h2 (Ne.symm hz)
      have hc : E2 ^ 2 * E2 ^ 2 ≤ (E0 * D) * E2 ^ 2 := by
        calc
          E2 ^ 2 * E2 ^ 2 = E2 ^ 4 := by ring
          _ ≤ (E0 * D) * E2 ^ 2 := hFourth
      exact (mul_le_mul_iff_of_pos_right (pow_pos hp 2)).mp hc
  constructor
  · calc
      E1 ^ 4 = (E1 ^ 2) ^ 2 := by ring
      _ ≤ (E0 * E2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg E1) h01 2
      _ = E0 ^ 2 * E2 ^ 2 := by ring
      _ ≤ E0 ^ 2 * (E0 * D) :=
        mul_le_mul_of_nonneg_left hMiddle (sq_nonneg E0)
      _ = E0 ^ 3 * D := by ring
  constructor
  · exact hMiddle
  · calc
      E3 ^ 4 = (E3 ^ 2) ^ 2 := by ring
      _ ≤ (E2 * D) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg E3) h23 2
      _ = E2 ^ 2 * D ^ 2 := by ring
      _ ≤ (E0 * D) * D ^ 2 :=
        mul_le_mul_of_nonneg_right hMiddle (sq_nonneg D)
      _ = E0 * D ^ 3 := by ring

/-- Coefficient-one four-step interpolation for the FULL physical Schwartz
energies E0/E1/E2/E3 and complete 243-slot fourth-derivative dissipation D. -/
theorem lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 4 ≤
        (lowNormalRealSchwartzH3Energy0 f) ^ 3 *
          lowNormalRealSchwartzH3TopDissipation f ∧
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
        lowNormalRealSchwartzH3Energy0 f *
          lowNormalRealSchwartzH3TopDissipation f ∧
    (lowNormalRealSchwartzH3Energy3 f) ^ 4 ≤
        lowNormalRealSchwartzH3Energy0 f *
          (lowNormalRealSchwartzH3TopDissipation f) ^ 3 := by
  exact criticalHalf_fiveOrder_adjacentCauchy_implies_quartic
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3Energy2 f)
    (lowNormalRealSchwartzH3Energy3 f)
    (lowNormalRealSchwartzH3TopDissipation f)
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3TopDissipation_nonneg f)
    (lowNormalRealSchwartzH3Energy1_sq_le_E0_mul_E2 f)
    (lowNormalRealSchwartzH3Energy2_sq_le_E1_mul_E3 f)
    (lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f)

/-- The second-order physical Schwartz energy is sharply bounded by the
geometric mean of E0 and the fourth-order quadratic dissipation. -/
theorem lowNormalRealSchwartzH3Energy2_sq_le_E0_mul_topDissipation
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy0 f *
        lowNormalRealSchwartzH3TopDissipation f :=
  (lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation f).2.1

/-- The first derivative block admits the exact fourth-power interpolation
between mass E0 and order-four dissipation D. -/
theorem lowNormalRealSchwartzH3Energy1_pow_four_le_E0_cube_mul_topDissipation
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 4 ≤
      (lowNormalRealSchwartzH3Energy0 f) ^ 3 *
        lowNormalRealSchwartzH3TopDissipation f :=
  (lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation f).1

/-- The third derivative block admits the exact fourth-power interpolation
between physical E0 and the full order-four dissipation D. -/
theorem lowNormalRealSchwartzH3Energy3_pow_four_le_E0_mul_topDissipation_cube
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy3 f) ^ 4 ≤
      lowNormalRealSchwartzH3Energy0 f *
        (lowNormalRealSchwartzH3TopDissipation f) ^ 3 :=
  (lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation f).2.2

/-- Strictly positive third-order mass forces strictly positive full
fourth-order dissipation. This follows from the proved fourth-order
coercivity and does not require a nondegeneracy theorem for E3 itself. -/
theorem lowNormalRealSchwartzH3Energy3_pos_implies_topDissipation_pos
    (f : A3 → SchwartzMap V3 ℝ)
    (h3 : 0 < lowNormalRealSchwartzH3Energy3 f) :
    0 < lowNormalRealSchwartzH3TopDissipation f := by
  have hD0 := lowNormalRealSchwartzH3TopDissipation_nonneg f
  by_contra hNot
  have hZero : lowNormalRealSchwartzH3TopDissipation f = 0 :=
    le_antisymm (le_of_not_gt hNot) hD0
  have hCoercive :=
    lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f
  rw [hZero, mul_zero] at hCoercive
  exact (not_lt_of_ge hCoercive) (pow_pos h3 2)

/-- The intrinsic nonlinear shape denominator is positive on every
positive-endpoint physical Schwartz profile, not only after normalizing. -/
theorem lowNormalRealSchwartz_positiveEndpoints_shapeDenominator_pos
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (h3 : 0 < lowNormalRealSchwartzH3Energy3 f) :
    0 < lowNormalRealSchwartz_sharpShapeDenominator f := by
  have hD := lowNormalRealSchwartzH3Energy3_pos_implies_topDissipation_pos f h3
  unfold lowNormalRealSchwartz_sharpShapeDenominator
  positivity

/-- On the already constructed E0=E3=1 orbit, all three quartic controls
hold with no endpoint factors. This specializes only proved physical bounds. -/
theorem lowNormalRealSchwartz_unitEndpoints_fiveOrder_corridor
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 4 ≤
        lowNormalRealSchwartzH3TopDissipation f ∧
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
        lowNormalRealSchwartzH3TopDissipation f ∧
    (1 : ℝ) ≤ (lowNormalRealSchwartzH3TopDissipation f) ^ 3 := by
  obtain ⟨hFirst, hSecond, hThird⟩ :=
    lowNormalRealSchwartzH3Energy_fiveOrder_sharpQuarticInterpolation f
  constructor
  · simpa only [h0, one_pow, one_mul] using hFirst
  constructor
  · simpa only [h0, one_mul] using hSecond
  · simpa only [h0, h3, one_pow, one_mul] using hThird

end
end PrimeTensor.FirstMonomialTriad
