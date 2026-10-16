import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzHolderSlotMassMultiplicities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact finite 2-4-4 Holder polynomial for the signed 243-slot monomial

The analytic 2-4-4 Holder theorem has already been proved for the actual
Schwartz first-monomial slots, and the 243-slot factor multiplicities have
been identified. The remaining *discrete* Holder step is a coefficient-one
real polynomial inequality, derived here by two finite Cauchy--Schwarz
applications. It is independent of all derivative and integral expressions.

A separate transfer lemma applies the inequality to the signed physical
first monomial, retaining its factor two. Its explicit `hSlot` argument is
the REAL form of the already proved extended-real pointwise Holder bound.
Discharging this norm-conversion premise is the next step; this module does
NOT assert that it has already been discharged and introduces no axiom.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeHolderDiscrete244 (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Two finite Cauchy--Schwarz steps yield the exact fourth-power
`2-4-4` Holder inequality, with coefficient one and no nonzero-mass
hypotheses. This holds for *signed* real arrays as well. -/
theorem lowNormal_finset_discreteHolder244_fourth
    {J : Type*} [Fintype J] (a b c : J → ℝ) :
    (∑ p : J, a p * (b p * c p)) ^ 4 ≤
      (∑ p : J, (a p) ^ 2) ^ 2 *
        ((∑ p : J, (b p) ^ 4) * (∑ p : J, (c p) ^ 4)) := by
  classical
  have hFirst :
      (∑ p : J, a p * (b p * c p)) ^ 2 ≤
        (∑ p : J, (a p) ^ 2) *
          (∑ p : J, (b p * c p) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
      a (fun p => b p * c p)
  have hSecond' :
      (∑ p : J, (b p) ^ 2 * (c p) ^ 2) ^ 2 ≤
        (∑ p : J, (b p) ^ 4) * (∑ p : J, (c p) ^ 4) := by
    have hCS :
        (∑ p : J, (b p) ^ 2 * (c p) ^ 2) ^ 2 ≤
          (∑ p : J, ((b p) ^ 2) ^ 2) *
            (∑ p : J, ((c p) ^ 2) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
        (fun p => (b p) ^ 2) (fun p => (c p) ^ 2)
    have hb :
        (∑ p : J, ((b p) ^ 2) ^ 2) =
          (∑ p : J, (b p) ^ 4) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have hc :
        (∑ p : J, ((c p) ^ 2) ^ 2) =
          (∑ p : J, (c p) ^ 4) := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hb, hc] at hCS
    exact hCS
  have hSecond :
      (∑ p : J, (b p * c p) ^ 2) ^ 2 ≤
        (∑ p : J, (b p) ^ 4) * (∑ p : J, (c p) ^ 4) := by
    simpa only [mul_pow] using hSecond'
  calc
    (∑ p : J, a p * (b p * c p)) ^ 4 =
        ((∑ p : J, a p * (b p * c p)) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ p : J, (a p) ^ 2) *
        (∑ p : J, (b p * c p) ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hFirst 2
    _ = (∑ p : J, (a p) ^ 2) ^ 2 *
          (∑ p : J, (b p * c p) ^ 2) ^ 2 := by ring
    _ ≤ (∑ p : J, (a p) ^ 2) ^ 2 *
          ((∑ p : J, (b p) ^ 4) * (∑ p : J, (c p) ^ 4)) :=
      mul_le_mul_of_nonneg_left hSecond (sq_nonneg _)

/-- A fivefold index is kept as a product, so the Cauchy--Schwarz
proof sees only one finite index rather than 243 nested Schwartz terms. -/
private abbrev FiveSlots := A3 × (A3 × (A3 × (A3 × A3)))

private abbrev rawSlot (f : A3 → SchwartzMap V3 ℝ) (p : FiveSlots) : ℝ :=
  lowNormalRealSchwartz_firstMonomialSlotIntegral f
    p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

private theorem rawSlot_sum_eq_firstMonomialSum
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ p : FiveSlots, rawSlot f p) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ r : A3, ∑ j : A3,
        lowNormalRealSchwartz_firstMonomialSlotIntegral f i k l r j := by
  classical
  simp only [FiveSlots, Fintype.sum_prod_type, rawSlot]

/-- Transfer the polynomial Holder bound to the *signed*, complete 243-slot
physical first monomial. `hSlot` is deliberately visible: it must be
supplied by the real-valued version of the already proved analytic Holder
bound. This lemma has no implicit positivity or PDE hypotheses. -/
theorem lowNormalRealSchwartz_firstMonomial_discrete244_transfer
    (f : A3 → SchwartzMap V3 ℝ)
    (a b c : FiveSlots → ℝ)
    (hSlot : ∀ p : FiveSlots,
      |rawSlot f p| ≤ a p * (b p * c p)) :
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 ≤
      (16 : ℝ) *
        ((∑ p : FiveSlots, (a p) ^ 2) ^ 2 *
          ((∑ p : FiveSlots, (b p) ^ 4) *
            (∑ p : FiveSlots, (c p) ^ 4))) := by
  classical
  have hM :
      lowNormalRealSchwartzPoint3Monomial f =
        2 * (∑ p : FiveSlots, rawSlot f p) := by
    rw [lowNormalRealSchwartz_firstMonomial_eq_twice_slotSum]
    congr 1
    exact (rawSlot_sum_eq_firstMonomialSum f).symm
  have hAbs :
      |∑ p : FiveSlots, rawSlot f p| ≤
        ∑ p : FiveSlots, a p * (b p * c p) :=
    (Finset.abs_sum_le_sum_abs (rawSlot f)
      (Finset.univ : Finset FiveSlots)).trans
      (Finset.sum_le_sum (fun p _ => hSlot p))
  have hEven :
      (∑ p : FiveSlots, rawSlot f p) ^ 4 =
        |∑ p : FiveSlots, rawSlot f p| ^ 4 := by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hDiscrete := lowNormal_finset_discreteHolder244_fourth a b c
  calc
    (lowNormalRealSchwartzPoint3Monomial f) ^ 4 =
        16 * ((∑ p : FiveSlots, rawSlot f p) ^ 4) := by
      rw [hM]
      ring
    _ = 16 * |∑ p : FiveSlots, rawSlot f p| ^ 4 := by
      rw [hEven]
    _ ≤ 16 * (∑ p : FiveSlots, a p * (b p * c p)) ^ 4 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hAbs 4) (by norm_num)
    _ ≤ 16 *
        ((∑ p : FiveSlots, (a p) ^ 2) ^ 2 *
          ((∑ p : FiveSlots, (b p) ^ 4) *
            (∑ p : FiveSlots, (c p) ^ 4))) :=
      mul_le_mul_of_nonneg_left hDiscrete (by norm_num)

end
end PrimeTensor.FirstMonomialTriad
