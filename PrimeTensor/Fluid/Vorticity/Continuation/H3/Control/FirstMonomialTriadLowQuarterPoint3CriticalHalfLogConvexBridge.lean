import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3CriticalHalfBalancedShape

/-!
# Log-convexity and the balanced critical-half shape bridge

The actual first monomial, full H3 energies and dissipation now carry proved
amplitude and spatial dilation laws.  The remaining uniform-shape issue is
not settled by those laws.  This file gives two division-free reductions.

First, adjacent Cauchy--Schwarz bounds E1² ≤ E0 E2 and E2² ≤ E1 E3 imply
E1³ ≤ E0² E3 and E2³ ≤ E0 E3².  Second, at a balanced positive scale
λ⁶ E3 = E0, these cubic inequalities imply

  E0 + λ² E1 + λ⁴ E2 + λ⁶ E3 ≤ 4 E0.

The scalar critical-half condition at this scale then implies the necessary
balanced polynomial shape threshold

  M¹² ≤ (4 C² D²)⁶ E0⁵ E3.

The final theorem transfers this necessary condition to genuine solenoidal
real Schwartz profiles, using existing physical Point3 dilation identities.
The adjacent Cauchy bounds are EXPLICIT HYPOTHESES, not falsely claimed as
proved for the real Schwartz H3 energies.  Fourier-to-Schwartz log-convexity
is a separate analytic task.  No uniform coefficient existence is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCriticalHalfLogConvex (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The two adjacent Cauchy inequalities imply the two cubic end-point
moment inequalities.  Neither cancellation divides by a potentially zero
moment: the corresponding zero cases are handled separately. -/
theorem criticalHalf_adjacentCauchy_implies_cubicLogConvex
    (E0 E1 E2 E3 : ℝ)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3)
    (h01 : E1 ^ 2 ≤ E0 * E2)
    (h12 : E2 ^ 2 ≤ E1 * E3) :
    E1 ^ 3 ≤ E0 ^ 2 * E3 ∧ E2 ^ 3 ≤ E0 * E3 ^ 2 := by
  have hFirstFourth : E1 ^ 4 ≤ E0 ^ 2 * (E1 * E3) := by
    calc
      E1 ^ 4 = (E1 ^ 2) ^ 2 := by ring
      _ ≤ (E0 * E2) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg E1) h01 2
      _ = E0 ^ 2 * E2 ^ 2 := by ring
      _ ≤ E0 ^ 2 * (E1 * E3) :=
        mul_le_mul_of_nonneg_left h12 (sq_nonneg E0)
  have hSecondFourth : E2 ^ 4 ≤ (E0 * E2) * E3 ^ 2 := by
    calc
      E2 ^ 4 = (E2 ^ 2) ^ 2 := by ring
      _ ≤ (E1 * E3) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg E2) h12 2
      _ = E1 ^ 2 * E3 ^ 2 := by ring
      _ ≤ (E0 * E2) * E3 ^ 2 :=
        mul_le_mul_of_nonneg_right h01 (sq_nonneg E3)
  constructor
  · by_cases hZero : E1 = 0
    · simpa [hZero] using mul_nonneg (sq_nonneg E0) hE3
    · have hPos : 0 < E1 := lt_of_le_of_ne hE1 (Ne.symm hZero)
      apply (mul_le_mul_iff_of_pos_right hPos).mp
      calc
        E1 ^ 3 * E1 = E1 ^ 4 := by ring
        _ ≤ E0 ^ 2 * (E1 * E3) := hFirstFourth
        _ = (E0 ^ 2 * E3) * E1 := by ring
  · by_cases hZero : E2 = 0
    · simpa [hZero] using mul_nonneg hE0 (sq_nonneg E3)
    · have hPos : 0 < E2 := lt_of_le_of_ne hE2 (Ne.symm hZero)
      apply (mul_le_mul_iff_of_pos_right hPos).mp
      calc
        E2 ^ 3 * E2 = E2 ^ 4 := by ring
        _ ≤ (E0 * E2) * E3 ^ 2 := hSecondFourth
        _ = (E0 * E3 ^ 2) * E2 := by ring

/-- The cubic log-convexity conditions control *both* intermediate H3
blocks at any positive balance scale λ⁶ E3 = E0. -/
theorem criticalHalf_balancedScale_energyPolynomial_upper
    (E0 E1 E2 E3 scale : ℝ)
    (hE0 : 0 < E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hscale : 0 < scale)
    (hInterp1 : E1 ^ 3 ≤ E0 ^ 2 * E3)
    (hInterp2 : E2 ^ 3 ≤ E0 * E3 ^ 2)
    (hBalance : scale ^ 6 * E3 = E0) :
    E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3 ≤ 4 * E0 := by
  have hOneCube : (scale ^ 2 * E1) ^ 3 ≤ E0 ^ 3 := by
    calc
      (scale ^ 2 * E1) ^ 3 = scale ^ 6 * E1 ^ 3 := by ring
      _ ≤ scale ^ 6 * (E0 ^ 2 * E3) :=
        mul_le_mul_of_nonneg_left hInterp1 (pow_nonneg hscale.le 6)
      _ = E0 ^ 3 := by
        calc
          scale ^ 6 * (E0 ^ 2 * E3) = E0 ^ 2 * (scale ^ 6 * E3) := by ring
          _ = E0 ^ 3 := by rw [hBalance]; ring
  have hTwoCube : (scale ^ 4 * E2) ^ 3 ≤ E0 ^ 3 := by
    calc
      (scale ^ 4 * E2) ^ 3 = scale ^ 12 * E2 ^ 3 := by ring
      _ ≤ scale ^ 12 * (E0 * E3 ^ 2) :=
        mul_le_mul_of_nonneg_left hInterp2 (pow_nonneg hscale.le 12)
      _ = E0 ^ 3 := by
        calc
          scale ^ 12 * (E0 * E3 ^ 2) = E0 * (scale ^ 6 * E3) ^ 2 := by ring
          _ = E0 ^ 3 := by rw [hBalance]; ring
  have hOne : scale ^ 2 * E1 ≤ E0 := by
    by_contra hn
    have hlt : E0 < scale ^ 2 * E1 := lt_of_not_ge hn
    have hc := pow_lt_pow_left₀ hlt hE0.le (by norm_num : (3 : ℕ) ≠ 0)
    exact (not_lt_of_ge hOneCube) hc
  have hTwo : scale ^ 4 * E2 ≤ E0 := by
    by_contra hn
    have hlt : E0 < scale ^ 4 * E2 := lt_of_not_ge hn
    have hc := pow_lt_pow_left₀ hlt hE0.le (by norm_num : (3 : ℕ) ≠ 0)
    exact (not_lt_of_ge hTwoCube) hc
  rw [hBalance]
  linarith

/-- The critical-half scalar inequality at a balanced scale forces a
polynomial threshold in the two endpoint masses.  The factor `4^6` is
not asserted optimal; it comes from summing four nonnegative H3 blocks. -/
theorem criticalHalf_balancedScale_polynomialNecessary
    (M D C E0 E1 E2 E3 scale : ℝ)
    (hE0 : 0 < E0) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (hE3 : 0 ≤ E3) (hscale : 0 < scale)
    (hInterp1 : E1 ^ 3 ≤ E0 ^ 2 * E3)
    (hInterp2 : E2 ^ 3 ≤ E0 * E3 ^ 2)
    (hBalance : scale ^ 6 * E3 = E0)
    (hScalar : M ^ 2 * scale ≤ C ^ 2 * D ^ 2 *
      (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3)) :
    M ^ 12 ≤ (4 * C ^ 2 * D ^ 2) ^ 6 * E0 ^ 5 * E3 := by
  have hUpper := criticalHalf_balancedScale_energyPolynomial_upper
    E0 E1 E2 E3 scale hE0 hE1 hE2 hscale hInterp1 hInterp2 hBalance
  have hBound : M ^ 2 * scale ≤ 4 * C ^ 2 * D ^ 2 * E0 := by
    calc
      _ ≤ C ^ 2 * D ^ 2 *
        (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) := hScalar
      _ ≤ C ^ 2 * D ^ 2 * (4 * E0) :=
        mul_le_mul_of_nonneg_left hUpper (by positivity)
      _ = 4 * C ^ 2 * D ^ 2 * E0 := by ring
  have hSix := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg M) hscale.le) hBound 6
  apply (mul_le_mul_iff_of_pos_right hE0).mp
  calc
    M ^ 12 * E0 = (M ^ 2 * scale) ^ 6 * E3 := by
      rw [← hBalance]
      ring
    _ ≤ (4 * C ^ 2 * D ^ 2 * E0) ^ 6 * E3 :=
      mul_le_mul_of_nonneg_right hSix hE3
    _ = ((4 * C ^ 2 * D ^ 2) ^ 6 * E0 ^ 5 * E3) * E0 := by
      ring

set_option maxHeartbeats 800000

/-- Physical corollary: if a coefficient controls the homogeneous
critical-half threshold on every *solenoidal* real Schwartz velocity, then
any single positive-monomial solenoidal profile satisfying the cubic
moment interpolation hypotheses obeys the balanced necessary inequality.
The moment inequalities are NOT assumed globally or hidden in a structure. -/
theorem lowNormalRealSchwartz_solenoidalBalancedShape_necessary
    (C scale : ℝ) (hscale : 0 < scale)
    (f : A3 → SchwartzMap V3 ℝ)
    (hDiv : lowNormalRealSchwartz_Point3Solenoidal f)
    (hM : 0 < lowNormalRealSchwartzPoint3Monomial f)
    (hE0 : 0 < lowNormalRealSchwartzH3Energy0 f)
    (hInterp1 : (lowNormalRealSchwartzH3Energy1 f) ^ 3 ≤
      (lowNormalRealSchwartzH3Energy0 f) ^ 2 *
        lowNormalRealSchwartzH3Energy3 f)
    (hInterp2 : (lowNormalRealSchwartzH3Energy2 f) ^ 3 ≤
      lowNormalRealSchwartzH3Energy0 f *
        (lowNormalRealSchwartzH3Energy3 f) ^ 2)
    (hBalance : scale ^ 6 * lowNormalRealSchwartzH3Energy3 f =
      lowNormalRealSchwartzH3Energy0 f)
    (hShape : ∀ g : A3 → SchwartzMap V3 ℝ,
      lowNormalRealSchwartz_Point3Solenoidal g →
      0 < lowNormalRealSchwartzPoint3Monomial g →
      (lowNormalRealSchwartzPoint3Monomial g) ^ 2 ≤
        C ^ 2 * (lowNormalRealSchwartzH3TopDissipation g) ^ 2 *
          lowNormalRealSchwartzH3EnergyQuadratic g) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
      (4 * C ^ 2 * (lowNormalRealSchwartzH3TopDissipation f) ^ 2) ^ 6 *
      (lowNormalRealSchwartzH3Energy0 f) ^ 5 *
      lowNormalRealSchwartzH3Energy3 f := by
  let M : ℝ := lowNormalRealSchwartzPoint3Monomial f
  let D : ℝ := lowNormalRealSchwartzH3TopDissipation f
  let E0 : ℝ := lowNormalRealSchwartzH3Energy0 f
  let E1 : ℝ := lowNormalRealSchwartzH3Energy1 f
  let E2 : ℝ := lowNormalRealSchwartzH3Energy2 f
  let E3 : ℝ := lowNormalRealSchwartzH3Energy3 f
  have hMscaled : 0 < lowNormalRealSchwartzPoint3Monomial
      (lowNormalSchwartzVelocityDilation scale hscale f) := by
    rw [lowNormalRealSchwartzPoint3Monomial_dilation]
    exact mul_pos (pow_pos hscale 4) hM
  have hBound := hShape (lowNormalSchwartzVelocityDilation scale hscale f)
    (lowNormalRealSchwartz_Point3Solenoidal_dilation scale hscale f hDiv)
    hMscaled
  rw [lowNormalRealSchwartzPoint3Monomial_dilation,
    lowNormalRealSchwartzH3TopDissipation_dilation,
    lowNormalRealSchwartzH3EnergyQuadratic_dilation] at hBound
  change (scale ^ 4 * M) ^ 2 ≤
    C ^ 2 * ((scale ^ 8 * (scale ^ 3)⁻¹) * D) ^ 2 *
      ((scale ^ 3)⁻¹ * E0 +
       (scale ^ 2 * (scale ^ 3)⁻¹) * E1 +
       (scale ^ 4 * (scale ^ 3)⁻¹) * E2 +
       (scale ^ 6 * (scale ^ 3)⁻¹) * E3) at hBound
  have hs : scale ≠ 0 := ne_of_gt hscale
  have hRight : C ^ 2 * ((scale ^ 8 * (scale ^ 3)⁻¹) * D) ^ 2 *
      ((scale ^ 3)⁻¹ * E0 +
       (scale ^ 2 * (scale ^ 3)⁻¹) * E1 +
       (scale ^ 4 * (scale ^ 3)⁻¹) * E2 +
       (scale ^ 6 * (scale ^ 3)⁻¹) * E3) =
      scale ^ 7 * (C ^ 2 * D ^ 2 *
        (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3)) := by
    field_simp [hs]
  have hScalar : M ^ 2 * scale ≤ C ^ 2 * D ^ 2 *
      (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3) := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos hscale 7)).mp
    calc
      scale ^ 7 * (M ^ 2 * scale) = (scale ^ 4 * M) ^ 2 := by ring
      _ ≤ _ := hBound
      _ = scale ^ 7 * (C ^ 2 * D ^ 2 *
        (E0 + scale ^ 2 * E1 + scale ^ 4 * E2 + scale ^ 6 * E3)) := hRight
  exact criticalHalf_balancedScale_polynomialNecessary
    M D C E0 E1 E2 E3 scale
    hE0
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3Energy2_nonneg f)
    (lowNormalRealSchwartzH3Energy3_nonneg f)
    hscale hInterp1 hInterp2 hBalance hScalar

end
end PrimeTensor.FirstMonomialTriad
