import PrimeTensor.Fluid.Vorticity.Continuation.H3.Control.FirstMonomialTriadLowQuarterPoint3SchwartzAdjacentSlotCauchy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Whole-energy Cauchy bounds assembled from actual Schwartz derivative slots

The preceding file proves two exact signed L2 Cauchy inequalities on every
real Schwartz component/direction slot.  This file combines the inequalities
by the finite-index Cauchy lemma, without any spectral bridge or unproved
integrability hypothesis.

The resulting whole-energy bounds are unconditional but incur one factor
`Fintype.card (Axis Depth.three)` (= 3). The diagonal order-two and order-three
subsum comparisons are proved directly from nonnegativity of every other
physical square-integral slot. Thus the resulting coefficient is deliberately
NOT the desired sharp coefficient 1.

Removing the factor three requires the Laplacian/Hessian mixed-derivative
contraction (equivalently a precise Fourier radial symbol identity), which
is not implied by diagonal slotwise Cauchy alone.
-/

namespace PrimeTensor.FirstMonomialTriad

open MeasureTheory PrimeTensor.Bridge.Euclidean
open scoped BigOperators SchwartzMap LineDeriv

noncomputable section

-- Nested physical derivative sums are large; give kernel reduction sufficient
-- heartbeats without changing the theorem statements or proof dependencies.
set_option maxHeartbeats 800000

private abbrev A3 := PrimeTensor.Axis Depth.three
private abbrev V3 := PrimeTensor.Bridge.Euclidean.H3FourierPoint3

noncomputable local instance axisFintypeAdjacentJointCauchy (d : Depth) :
    Fintype (PrimeTensor.Axis d) := Fintype.ofFinite (PrimeTensor.Axis d)


/-! The diagonal-subsum arguments are deliberately proved at the level of
finite real arrays.  Instantiating these lemmas below avoids reduction of the
Schwartz derivative operators during finite-set reasoning. -/

private theorem lowNormal_joint_diagonal_subsum
    {J I : Type*} [Fintype J] [Fintype I]
    (a : J → I → I → ℝ)
    (ha : ∀ j i k, 0 ≤ a j i k) :
    (∑ j, ∑ i, a j i i) ≤ (∑ j, ∑ i, ∑ k, a j i k) := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun k => a j i k)
    (fun k _ => ha j i k)
    (Finset.mem_univ i)

private theorem lowNormal_joint_middle_diagonal_subsum
    {J I K : Type*} [Fintype J] [Fintype I] [Fintype K]
    (a : J → I → I → K → ℝ)
    (ha : ∀ j i m k, 0 ≤ a j i m k) :
    (∑ j, ∑ i, ∑ k, a j i i k) ≤
      (∑ j, ∑ i, ∑ m, ∑ k, a j i m k) := by
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun m => ∑ k, a j i m k)
    (by
      intro m _
      exact Finset.sum_nonneg (fun k _ => ha j i m k))
    (Finset.mem_univ i)


/-- Pure scalar transport of a joint bound through a replication identity
and a nonnegative diagonal subsum. The Schwartz expressions never occur in
this proof: all elaboration is over five real numbers. -/
private theorem lowNormal_joint_bound_transfer
    {m a b d e : ℝ}
    (hJoint : m ^ 2 ≤ a * b)
    (hRep : a = d)
    (hDiag : b ≤ e)
    (hd : 0 ≤ d) :
    m ^ 2 ≤ d * e := by
  calc
    m ^ 2 ≤ a * b := hJoint
    _ = d * b := congrArg (fun t : ℝ => t * b) hRep
    _ ≤ d * e := mul_le_mul_of_nonneg_left hDiag hd

/-! Finite-dimensional Cauchy and replication identities.  Keep every proof
below at the level of real arrays, to avoid reducing Schwartz operators and
large integral expressions during the `Finset` argument. -/

private theorem lowNormal_joint_pair_cauchy
    {J I : Type*} [Fintype J] [Fintype I]
    (a b c : J → I → ℝ)
    (ha : ∀ j i, 0 ≤ a j i)
    (hc : ∀ j i, 0 ≤ c j i)
    (hb : ∀ j i, (b j i) ^ 2 ≤ a j i * c j i) :
    (∑ j, ∑ i, b j i) ^ 2 ≤
      (∑ j, ∑ i, a j i) * (∑ j, ∑ i, c j i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (J × I))
    (r := fun p : J × I => b p.1 p.2)
    (f := fun p : J × I => a p.1 p.2)
    (g := fun p : J × I => c p.1 p.2)
    (by intro p _; exact ha p.1 p.2)
    (by intro p _; exact hc p.1 p.2)
    (by intro p _; exact hb p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

private theorem lowNormal_joint_triple_cauchy
    {J I K : Type*} [Fintype J] [Fintype I] [Fintype K]
    (a b c : J → I → K → ℝ)
    (ha : ∀ j i k, 0 ≤ a j i k)
    (hc : ∀ j i k, 0 ≤ c j i k)
    (hb : ∀ j i k, (b j i k) ^ 2 ≤ a j i k * c j i k) :
    (∑ j, ∑ i, ∑ k, b j i k) ^ 2 ≤
      (∑ j, ∑ i, ∑ k, a j i k) *
        (∑ j, ∑ i, ∑ k, c j i k) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (J × (I × K)))
    (r := fun p : J × (I × K) => b p.1 p.2.1 p.2.2)
    (f := fun p : J × (I × K) => a p.1 p.2.1 p.2.2)
    (g := fun p : J × (I × K) => c p.1 p.2.1 p.2.2)
    (by intro p _; exact ha p.1 p.2.1 p.2.2)
    (by intro p _; exact hc p.1 p.2.1 p.2.2)
    (by intro p _; exact hb p.1 p.2.1 p.2.2)
  simpa only [Fintype.sum_prod_type] using h

private theorem lowNormal_joint_repeat_one
    {J I : Type*} [Fintype J] [Fintype I]
    (a : J → ℝ) :
    (∑ j, ∑ _i : I, a j) =
      (Fintype.card I : ℝ) * (∑ j, a j) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

private theorem lowNormal_joint_repeat_two
    {J I K : Type*} [Fintype J] [Fintype I] [Fintype K]
    (a : J → K → ℝ) :
    (∑ j, ∑ _i : I, ∑ k, a j k) =
      (Fintype.card I : ℝ) * (∑ j, ∑ k, a j k) := by
  calc
    _ = ∑ j, ∑ k, ∑ _i : I, a j k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum]


/-- Cauchy combined over all nine component/direction slots. -/
theorem lowNormalRealSchwartzH3Energy1_sq_le_joint_diagonal
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 2 ≤
      (∑ j : A3, ∑ i : A3, ∫ x : V3, (f j x) ^ 2) *
        (∑ j : A3, ∑ i : A3, ∫ x : V3,
          ((∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection i} (f j))) x) ^ 2) := by
  let a : A3 → A3 → ℝ := fun j _i => ∫ x : V3, (f j x) ^ 2
  let b : A3 → A3 → ℝ := fun j i => ∫ x : V3,
    ((∂_{h3FourierAxisDirection i} (f j)) x) ^ 2
  let c : A3 → A3 → ℝ := fun j i => ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection i} (f j))) x) ^ 2
  have h := lowNormal_joint_pair_cauchy a b c
    (by intro j _i; exact integral_nonneg (fun x => sq_nonneg (f j x)))
    (by intro j i; exact integral_nonneg (fun x =>
      sq_nonneg ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i} (f j))) x)))
    (by intro j i; exact lowNormalRealSchwartzH3Energy1_slot_cauchy f j i)
  change (∑ j : A3, ∑ i : A3, b j i) ^ 2 ≤
    (∑ j : A3, ∑ i : A3, a j i) *
      (∑ j : A3, ∑ i : A3, c j i)
  exact h

/-- The diagonal order-two squares form a nonnegative subsum of E2. -/
theorem lowNormalRealSchwartzH3Energy2_diagonal_le_full
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i} (f j))) x) ^ 2) ≤
      lowNormalRealSchwartzH3Energy2 f := by
  let a : A3 → A3 → A3 → ℝ := fun j i k =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2
  have ha : ∀ j i k, 0 ≤ a j i k := by
    intro j i k
    exact integral_nonneg (fun x =>
      sq_nonneg ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j))) x))
  have h := lowNormal_joint_diagonal_subsum a ha
  change (∑ j : A3, ∑ i : A3, a j i i) ≤
    (∑ j : A3, ∑ i : A3, ∑ k : A3, a j i k)
  exact h

/-- Unconditional E1² <= card(A3) E0 E2 (factor three). -/
theorem lowNormalRealSchwartzH3Energy1_sq_le_axisCard_mul_E0_E2
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy1 f) ^ 2 ≤
      (Fintype.card A3 : ℝ) *
        lowNormalRealSchwartzH3Energy0 f *
        lowNormalRealSchwartzH3Energy2 f := by
  have hJoint := lowNormalRealSchwartzH3Energy1_sq_le_joint_diagonal f
  have hDiag := lowNormalRealSchwartzH3Energy2_diagonal_le_full f
  have hRep :
      (∑ j : A3, ∑ i : A3, ∫ x : V3, (f j x) ^ 2) =
        (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy0 f := by
    change (∑ j : A3, ∑ i : A3,
      (fun j : A3 => ∫ x : V3, (f j x) ^ 2) j) =
      (Fintype.card A3 : ℝ) *
        (∑ j : A3, (fun j : A3 => ∫ x : V3, (f j x) ^ 2) j)
    exact lowNormal_joint_repeat_one _
  have hFirst : 0 ≤ (Fintype.card A3 : ℝ) *
      lowNormalRealSchwartzH3Energy0 f := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (lowNormalRealSchwartzH3Energy0_nonneg f)
  -- The large Fourier-free expressions are arguments of a scalar theorem.
  -- In particular, do not `rw` or `calc` inside the physical integral sums.
  exact lowNormal_joint_bound_transfer hJoint hRep hDiag hFirst

/-- Cauchy combined over all 27 component/direction/direction slots. -/
theorem lowNormalRealSchwartzH3Energy2_sq_le_joint_diagonal
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) *
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection i}
            (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2) := by
  let a : A3 → A3 → A3 → ℝ := fun j _i k => ∫ x : V3,
    ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2
  let b : A3 → A3 → A3 → ℝ := fun j i k => ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection k} (f j))) x) ^ 2
  let c : A3 → A3 → A3 → ℝ := fun j i k => ∫ x : V3,
    ((∂_{h3FourierAxisDirection i}
      (∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2
  have h := lowNormal_joint_triple_cauchy a b c
    (by intro j _i k; exact integral_nonneg (fun x =>
      sq_nonneg ((∂_{h3FourierAxisDirection k} (f j)) x)))
    (by intro j i k; exact integral_nonneg (fun x =>
      sq_nonneg ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)))) x)))
    (by intro j i k; exact lowNormalRealSchwartzH3Energy2_slot_cauchy f j i k)
  change (∑ j : A3, ∑ i : A3, ∑ k : A3, b j i k) ^ 2 ≤
    (∑ j : A3, ∑ i : A3, ∑ k : A3, a j i k) *
      (∑ j : A3, ∑ i : A3, ∑ k : A3, c j i k)
  exact h

/-- The repeated-middle-index order-three squares form a subsum of E3. -/
theorem lowNormalRealSchwartzH3Energy3_diagonal_le_full
    (f : A3 → SchwartzMap V3 ℝ) :
    (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection i}
          (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2) ≤
      lowNormalRealSchwartzH3Energy3 f := by
  let a : A3 → A3 → A3 → A3 → ℝ := fun j i m k =>
    ∫ x : V3,
      ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection m}
          (∂_{h3FourierAxisDirection k} (f j)))) x) ^ 2
  have ha : ∀ j i m k, 0 ≤ a j i m k := by
    intro j i m k
    exact integral_nonneg (fun x =>
      sq_nonneg ((∂_{h3FourierAxisDirection i}
        (∂_{h3FourierAxisDirection m}
          (∂_{h3FourierAxisDirection k} (f j)))) x))
  have h := lowNormal_joint_middle_diagonal_subsum a ha
  change (∑ j : A3, ∑ i : A3, ∑ k : A3, a j i i k) ≤
    (∑ j : A3, ∑ i : A3, ∑ m : A3, ∑ k : A3, a j i m k)
  exact h

/-- Unconditional E2² <= card(A3) E1 E3 (factor three). -/
theorem lowNormalRealSchwartzH3Energy2_sq_le_axisCard_mul_E1_E3
    (f : A3 → SchwartzMap V3 ℝ) :
    (lowNormalRealSchwartzH3Energy2 f) ^ 2 ≤
      (Fintype.card A3 : ℝ) *
        lowNormalRealSchwartzH3Energy1 f *
        lowNormalRealSchwartzH3Energy3 f := by
  have hJoint := lowNormalRealSchwartzH3Energy2_sq_le_joint_diagonal f
  have hDiag := lowNormalRealSchwartzH3Energy3_diagonal_le_full f
  have hRep :
      (∑ j : A3, ∑ i : A3, ∑ k : A3, ∫ x : V3,
        ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) =
        (Fintype.card A3 : ℝ) * lowNormalRealSchwartzH3Energy1 f := by
    change (∑ j : A3, ∑ i : A3, ∑ k : A3,
      (fun j k => ∫ x : V3,
        ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) j k) =
      (Fintype.card A3 : ℝ) *
        (∑ j : A3, ∑ k : A3,
          (fun j k => ∫ x : V3,
            ((∂_{h3FourierAxisDirection k} (f j)) x) ^ 2) j k)
    exact lowNormal_joint_repeat_two _
  have hFirst : 0 ≤ (Fintype.card A3 : ℝ) *
      lowNormalRealSchwartzH3Energy1 f := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (lowNormalRealSchwartzH3Energy1_nonneg f)
  exact lowNormal_joint_bound_transfer hJoint hRep hDiag hFirst

end
end PrimeTensor.FirstMonomialTriad
