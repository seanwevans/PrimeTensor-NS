import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzUnitShapeReduction
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sharp fourth-order coercivity from real Schwartz integration by parts

The coefficient-one adjacent Schwartz estimates extend to the fourth
spatial derivative.  Work first with an arbitrary FINITE family of Schwartz
functions, using the exact signed Laplacian pairing, whole-family Cauchy,
and the previously proved Hessian/Laplacian identity.  Then apply the family
theorem to every ordered second derivative of a physical velocity, with all
3 x 3 x 3 component/axis/axis slots retained.

The exact physical result is E3^2 <= E2 * D, where D is the project's
243-slot fourth derivative dissipation, not a new surrogate.
On the E0=E3=1 orbit, sharp E2<=1 then forces D>=1. Thus the normalized
shape quotient has a strictly positive denominator without assuming it.
No nonlinear estimate for the signed first monomial is asserted.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeFourthCoercivity (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)

/-- Finite-family coefficient-one interpolation: one full gradient block
between the actual zeroth block and full ordered Hessian block. -/
theorem lowNormalSchwartz_family_firstDerivative_sq_le_zero_mul_second
    {J : Type*} [Fintype J] (F : J → SchwartzMap V3 ℝ) :
    (∑ j : J, ∑ i : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i} (F j) : SchwartzMap V3 ℝ) x) ^ 2) ^ 2 ≤
    (∑ j : J, ∫ x : V3, (F j x) ^ 2) *
    (∑ j : J, ∑ i : A3, ∑ k : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (F j)) : SchwartzMap V3 ℝ) x) ^ 2) := by
  classical
  let B : ℝ := ∑ j : J, ∫ x : V3,
    F j x * lowNormalSchwartz_axisLaplacianMap (F j) x
  let A : ℝ := ∑ j : J, ∫ x : V3, (F j x) ^ 2
  let C : ℝ := ∑ j : J, ∫ x : V3,
    (lowNormalSchwartz_axisLaplacianMap (F j) x) ^ 2
  have hCS : B ^ 2 ≤ A * C := by
    dsimp only [A, B, C]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset J)
      (r := fun j => ∫ x : V3,
        F j x * lowNormalSchwartz_axisLaplacianMap (F j) x)
      (f := fun j => ∫ x : V3, (F j x) ^ 2)
      (g := fun j => ∫ x : V3,
        (lowNormalSchwartz_axisLaplacianMap (F j) x) ^ 2)
      (by intro j _; exact integral_nonneg (fun x => sq_nonneg (F j x)))
      (by intro j _; exact integral_nonneg (fun x =>
        sq_nonneg (lowNormalSchwartz_axisLaplacianMap (F j) x)))
      (by
        intro j _
        exact lowNormalSchwartz_integral_mul_sq_le
          (F j) (lowNormalSchwartz_axisLaplacianMap (F j)))
  have hPair :
      (∑ j : J, ∑ i : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i} (F j) : SchwartzMap V3 ℝ) x) ^ 2) =
      -B := by
    calc
      _ = ∑ j : J, -(∫ x : V3,
          F j x * lowNormalSchwartz_axisLaplacianMap (F j) x) := by
            apply Finset.sum_congr rfl
            intro j _
            exact lowNormalSchwartz_firstSquares_eq_neg_laplacian_pair (F j)
      _ = -B := by
        -- The named `B` is a `let`; identify it explicitly before
        -- applying the finite-sum negation identity.
        dsimp only [B]
        simp only [Finset.sum_neg_distrib]
  have hHess :
      C = (∑ j : J, ∑ i : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (F j)) : SchwartzMap V3 ℝ) x) ^ 2) := by
    dsimp only [C]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∫ x : V3, (lowNormalSchwartz_axisLaplacianMap (F j) x) ^ 2) =
          ∫ x : V3, (lowNormalSchwartz_axisLaplacian (F j) x) ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [lowNormalSchwartz_axisLaplacianMap_apply]
      _ = _ := lowNormalSchwartz_axisLaplacian_sq_integral_eq_hessian (F j)
  calc
    _ = B ^ 2 := by rw [hPair]; ring
    _ ≤ A * C := hCS
    _ = _ := by rw [hHess]

/-- A purely finite-index rotation that moves the last derivative axis
to the front, without simplifying any Schwartz derivative expression. -/
private theorem lowNormal_fourth_rotate_three
    (a : A3 → A3 → A3 → ℝ) :
    (∑ k : A3, ∑ l : A3, ∑ i : A3, a i k l) =
      ∑ i : A3, ∑ k : A3, ∑ l : A3, a i k l := by
  calc
    _ = ∑ k : A3, ∑ i : A3, ∑ l : A3, a i k l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The double derivative directions move together before the two old
indices; only ordinary finite sum commutativity is used. -/
private theorem lowNormal_fourth_rotate_four
    (a : A3 → A3 → A3 → A3 → ℝ) :
    (∑ k : A3, ∑ l : A3, ∑ i : A3, ∑ m : A3, a i m k l) =
      ∑ i : A3, ∑ m : A3, ∑ k : A3, ∑ l : A3, a i m k l := by
  calc
    _ = ∑ k : A3, ∑ i : A3, ∑ l : A3, ∑ m : A3, a i m k l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ i : A3, ∑ k : A3, ∑ l : A3, ∑ m : A3, a i m k l := Finset.sum_comm
    _ = ∑ i : A3, ∑ k : A3, ∑ m : A3, ∑ l : A3, a i m k l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

/-- Exact coefficient-one fourth derivative coercivity for genuine
physical Schwartz velocities. E2, E3 and D retain *all* their ordered
27, 81 and 243 slots respectively. -/
theorem lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy3 f) ^ 2 ≤
      lowNormalRealSchwartzH3Energy2 f *
        lowNormalRealSchwartzH3TopDissipation f := by
  let J := A3 × (A3 × A3)
  let F : J → SchwartzMap V3 ℝ := fun p =>
    ∂_{h3FourierAxisDirection p.2.1}
      (∂_{h3FourierAxisDirection p.2.2} (f p.1))
  have hGeneric := lowNormalSchwartz_family_firstDerivative_sq_le_zero_mul_second F
  have hZero :
      (∑ p : J, ∫ x : V3, (F p x) ^ 2) =
        lowNormalRealSchwartzH3Energy2 f := by
    -- Unfold the *local* family `F` explicitly: sum-product rewriting
    -- alone leaves `F (j, k, l)` opaque to the simplifier.
    change (∑ p : A3 × (A3 × A3), ∫ x : V3,
        ((∂_{h3FourierAxisDirection p.2.1}
          (∂_{h3FourierAxisDirection p.2.2} (f p.1)) : SchwartzMap V3 ℝ) x) ^ 2) =
      ∑ j : A3, ∑ k : A3, ∑ l : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l} (f j)) : SchwartzMap V3 ℝ) x) ^ 2
    simp only [Fintype.sum_prod_type]
  let a3 : A3 → A3 → A3 → A3 → ℝ := fun j i k l =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k}
          (∂_{h3FourierAxisDirection l} (f j))) : SchwartzMap V3 ℝ) x) ^ 2
  have hOne :
      (∑ p : J, ∑ i : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i} (F p) : SchwartzMap V3 ℝ) x) ^ 2) =
        lowNormalRealSchwartzH3Energy3 f := by
    calc
      _ = ∑ j : A3, ∑ k : A3, ∑ l : A3, ∑ i : A3, a3 j i k l := by
        change (∑ p : A3 × (A3 × A3), ∑ i : A3,
          a3 p.1 i p.2.1 p.2.2) = _
        simp only [Fintype.sum_prod_type]
      _ = ∑ j : A3, ∑ i : A3, ∑ k : A3, ∑ l : A3, a3 j i k l := by
        apply Finset.sum_congr rfl
        intro j _
        exact lowNormal_fourth_rotate_three (fun i k l => a3 j i k l)
      _ = lowNormalRealSchwartzH3Energy3 f := rfl
  let a4 : A3 → A3 → A3 → A3 → A3 → ℝ := fun j i m k l =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection m}
          (∂_{h3FourierAxisDirection k}
            (∂_{h3FourierAxisDirection l} (f j)))) : SchwartzMap V3 ℝ) x) ^ 2
  have hTwo :
      (∑ p : J, ∑ i : A3, ∑ m : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection m} (F p)) : SchwartzMap V3 ℝ) x) ^ 2) =
        lowNormalRealSchwartzH3TopDissipation f := by
    calc
      _ = ∑ j : A3, ∑ k : A3, ∑ l : A3, ∑ i : A3, ∑ m : A3,
            a4 j i m k l := by
        change (∑ p : A3 × (A3 × A3), ∑ i : A3, ∑ m : A3,
          a4 p.1 i m p.2.1 p.2.2) = _
        simp only [Fintype.sum_prod_type]
      _ = ∑ j : A3, ∑ i : A3, ∑ m : A3, ∑ k : A3, ∑ l : A3,
            a4 j i m k l := by
        apply Finset.sum_congr rfl
        intro j _
        exact lowNormal_fourth_rotate_four (fun i m k l => a4 j i m k l)
      _ = lowNormalRealSchwartzH3TopDissipation f := rfl
  -- The large physical expressions are transported through three equalities,
  -- with no rewriting of directional-derivative syntax inside an inequality.
  calc
    (lowNormalRealSchwartzH3Energy3 f) ^ 2 =
        (∑ p : J, ∑ i : A3, ∫ x : V3,
          ((∂_{h3FourierAxisDirection i} (F p) : SchwartzMap V3 ℝ) x) ^ 2) ^ 2 := by
            rw [hOne]
    _ ≤ (∑ p : J, ∫ x : V3, (F p x) ^ 2) *
        (∑ p : J, ∑ i : A3, ∑ m : A3, ∫ x : V3,
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection m} (F p)) : SchwartzMap V3 ℝ) x) ^ 2) :=
              hGeneric
    _ = _ := by rw [hZero, hTwo]

/-- The normalized unit-endpoint Schwartz orbit automatically has
fourth-order dissipation >= 1.  In particular D cannot vanish there. -/
theorem lowNormalRealSchwartz_unitEndpoints_topDissipation_ge_one
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    (1 : ℝ) ≤ lowNormalRealSchwartzH3TopDissipation f := by
  have hE2 := (lowNormalRealSchwartz_unitEndpoints_intermediate_le_one f h0 h3).2
  have hD := lowNormalRealSchwartzH3TopDissipation_nonneg f
  have hCoercive := lowNormalRealSchwartzH3Energy3_sq_le_E2_mul_topDissipation f
  have hLower : (1 : ℝ) ≤
      lowNormalRealSchwartzH3Energy2 f * lowNormalRealSchwartzH3TopDissipation f := by
    simpa only [h3, one_pow] using hCoercive
  have hUpper := mul_le_mul_of_nonneg_right hE2 hD
  have hUpper' : lowNormalRealSchwartzH3Energy2 f *
      lowNormalRealSchwartzH3TopDissipation f ≤
        lowNormalRealSchwartzH3TopDissipation f := by
    simpa only [one_mul] using hUpper
  exact hLower.trans hUpper'

/-- A positive shape denominator follows from unit endpoints without
assuming D>0 independently. -/
theorem lowNormalRealSchwartz_unitEndpoints_shapeDenominator_pos
    (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    0 < lowNormalRealSchwartz_sharpShapeDenominator f := by
  have hD : 0 < lowNormalRealSchwartzH3TopDissipation f :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (lowNormalRealSchwartz_unitEndpoints_topDissipation_ge_one f h0 h3)
  unfold lowNormalRealSchwartz_sharpShapeDenominator
  rw [h0, h3]
  positivity

/-- The earlier normalized ratio/monomial equivalence no longer needs
an independent positivity assumption on D. -/
theorem lowNormalRealSchwartz_unitEndpoints_ratio_le_iff_monomial_autoD
    (K : ℝ) (f : A3 → SchwartzMap V3 ℝ)
    (h0 : lowNormalRealSchwartzH3Energy0 f = 1)
    (h3 : lowNormalRealSchwartzH3Energy3 f = 1) :
    lowNormalRealSchwartz_sharpShapeRatio f ≤ K ↔
      (lowNormalRealSchwartzPoint3Monomial f) ^ 12 ≤
        K * (lowNormalRealSchwartzH3TopDissipation f) ^ 12 := by
  have hD : 0 < lowNormalRealSchwartzH3TopDissipation f :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (lowNormalRealSchwartz_unitEndpoints_topDissipation_ge_one f h0 h3)
  exact lowNormalRealSchwartz_unitEndpoints_ratio_le_iff_monomial K f h0 h3 hD

end
end PrimeTensor.FirstMonomialTriad
