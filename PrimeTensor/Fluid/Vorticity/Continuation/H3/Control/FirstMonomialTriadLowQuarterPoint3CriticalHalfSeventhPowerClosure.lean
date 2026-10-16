import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzFiveOrderInterpolation

/-!
# Exact seventh-power algebra behind the classical critical-half Sobolev estimate

For the real physical 243-slot first monomial, the standard estimate is

    |M| <= C ||u||_(dot H^(1/2)) ||u||_(dot H^4)^2.

This module isolates the precise integer-power algebra required to combine
L²-L⁴-L⁴ Hölder, the fractional Sobolev L⁴ step, and interpolation.
It does NOT assert the required Sobolev inequalities themselves: those
are still the next analytic formalization task. In particular the predicate
of this module is not an automatic consequence of `SchwartzMap.memLp`.

Write H for the order-three L² norm, Q for the product of the two order-two
L⁴ norms (and any finite aggregation factor), A for the homogeneous half
norm, and B for the fourth-derivative L² norm. The hypotheses

    H^7 <= A^2 * B^5,      Q^7 <= K^7 * A^5 * B^9

combine to

    H*Q <= K*A*B^2.

The proof is division-free and valid at A=0, B=0, H=0, or Q=0. This
is only an EXACT EXPONENT CLOSURE, not yet an established quantitative
fractional Sobolev estimate for Schwartz maps.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeCriticalHalfSeventhPower (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- The sharp algebraic interpolation exponents for the 2-4-4 first monomial.
The only constant is the quantitative L⁴/Sobolev factor `K`, which is NOT
produced by this scalar lemma. -/
theorem criticalHalf_seventhPower_holderSobolev_closure
    (M H Q A B K : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hM : |M| ≤ H * Q)
    (hInterp3 : H ^ 7 ≤ A ^ 2 * B ^ 5)
    (hSobolev4 : Q ^ 7 ≤ K ^ 7 * A ^ 5 * B ^ 9) :
    |M| ≤ K * A * B ^ 2 := by
  have hLowerNonneg : 0 ≤ A ^ 2 * B ^ 5 := by positivity
  have hQpowNonneg : 0 ≤ Q ^ 7 := pow_nonneg hQ _
  have hSeventh : (H * Q) ^ 7 ≤ (K * A * B ^ 2) ^ 7 := by
    calc
      (H * Q) ^ 7 = H ^ 7 * Q ^ 7 := by ring
      _ ≤ (A ^ 2 * B ^ 5) * (K ^ 7 * A ^ 5 * B ^ 9) :=
        mul_le_mul hInterp3 hSobolev4 hQpowNonneg hLowerNonneg
      _ = (K * A * B ^ 2) ^ 7 := by ring
  have hProduct : H * Q ≤ K * A * B ^ 2 := by
    by_contra hn
    have hlt : K * A * B ^ 2 < H * Q := lt_of_not_ge hn
    have hp : (K * A * B ^ 2) ^ 7 < (H * Q) ^ 7 :=
      pow_lt_pow_left₀ hlt (by positivity)
        (by norm_num : (7 : ℕ) ≠ 0)
    exact (not_lt_of_ge hSeventh) hp
  exact hM.trans hProduct

/-- The scalar critical-half energy closure after proving the Ḣ^(1/2)
quadratic estimate and identifying the fourth-order norm squared with D.
Neither of these inputs is inferred from a conditional PDE hypothesis. -/
theorem criticalHalf_seventhPower_to_quadraticEnergy
    (M H Q A B K E0 E1 D : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hD : 0 ≤ D)
    (hM : |M| ≤ H * Q)
    (hInterp3 : H ^ 7 ≤ A ^ 2 * B ^ 5)
    (hSobolev4 : Q ^ 7 ≤ K ^ 7 * A ^ 5 * B ^ 9)
    (hHalf : A ^ 2 ≤ E0 + E1)
    (hTop : B ^ 2 = D) :
    |M| ≤ K * Real.sqrt (E0 + E1) * D := by
  have hCritical := criticalHalf_seventhPower_holderSobolev_closure
    M H Q A B K hH hQ hA hB hK hM hInterp3 hSobolev4
  have hSumNonneg : 0 ≤ E0 + E1 := add_nonneg hE0 hE1
  have hRootNonneg : 0 ≤ Real.sqrt (E0 + E1) := Real.sqrt_nonneg _
  have hRootSq : (Real.sqrt (E0 + E1)) ^ 2 = E0 + E1 :=
    Real.sq_sqrt hSumNonneg
  have hARoot : A ≤ Real.sqrt (E0 + E1) := by
    nlinarith
  calc
    |M| ≤ K * A * B ^ 2 := hCritical
    _ = (K * A) * D := by rw [hTop]
    _ ≤ (K * Real.sqrt (E0 + E1)) * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hARoot hK) hD
    _ = K * Real.sqrt (E0 + E1) * D := rfl

/-- The exact physical Schwartz specialization of the preceding algebra.
To obtain an unconditional bound, one must CONSTRUCT H,Q,A,B,K with the
listed quantitative L⁴ and fractional interpolation estimates; no such
construction is assumed or claimed by this theorem. -/
theorem lowNormalRealSchwartz_criticalHalf_of_seventhPowerAnalyticInputs
    (f : A3 → SchwartzMap V3 ℝ)
    (H Q A B K : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hM : |lowNormalRealSchwartzPoint3Monomial f| ≤ H * Q)
    (hInterp3 : H ^ 7 ≤ A ^ 2 * B ^ 5)
    (hSobolev4 : Q ^ 7 ≤ K ^ 7 * A ^ 5 * B ^ 9)
    (hHalf : A ^ 2 ≤
      lowNormalRealSchwartzH3Energy0 f + lowNormalRealSchwartzH3Energy1 f)
    (hTop : B ^ 2 = lowNormalRealSchwartzH3TopDissipation f) :
    |lowNormalRealSchwartzPoint3Monomial f| ≤
      K * Real.sqrt
          (lowNormalRealSchwartzH3Energy0 f +
            lowNormalRealSchwartzH3Energy1 f) *
        lowNormalRealSchwartzH3TopDissipation f := by
  exact criticalHalf_seventhPower_to_quadraticEnergy
    (lowNormalRealSchwartzPoint3Monomial f) H Q A B K
    (lowNormalRealSchwartzH3Energy0 f)
    (lowNormalRealSchwartzH3Energy1 f)
    (lowNormalRealSchwartzH3TopDissipation f)
    hH hQ hA hB hK
    (lowNormalRealSchwartzH3Energy0_nonneg f)
    (lowNormalRealSchwartzH3Energy1_nonneg f)
    (lowNormalRealSchwartzH3TopDissipation_nonneg f)
    hM hInterp3 hSobolev4 hHalf hTop

end
end PrimeTensor.FirstMonomialTriad
