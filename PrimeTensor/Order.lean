import PrimeTensor.MulRat

/-!
# Native order and multiplicative annuli on `MulRat`

The strict order is inherited from positive cross-product comparison of
`PrimeRatio` representatives.  No ordinary rational or real is used.

This gives the native notion needed for multiplicative Cauchy convergence:
`a` and `b` are within a multiplicative tolerance `δ > 1` when both
`a / b < δ` and `b / a < δ`.
-/

namespace PrimeTensor

namespace PrimeRatio

private theorem multiset_eval_pos_order (q : PrimeMultiset) : 0 < q.eval := by
  refine Quotient.inductionOn q ?_
  intro b
  exact lt_of_lt_of_le Nat.zero_lt_one (PrimeBag.one_le_eval b)

/-- Replacing the left argument by an equivalent ratio preserves strict order. -/
private theorem lt_of_same_left {a a' b : PrimeRatio}
    (ha : Same a a') (h : Lt a b) : Lt a' b := by
  unfold Same at ha
  unfold Lt at h ⊢
  exact (Nat.mul_lt_mul_right (multiset_eval_pos_order a.lower)).mp (by
    calc
      (a'.upper.eval * b.lower.eval) * a.lower.eval
          = (a'.upper.eval * a.lower.eval) * b.lower.eval := by ac_rfl
      _ = (a.upper.eval * a'.lower.eval) * b.lower.eval := by rw [← ha]
      _ = (a.upper.eval * b.lower.eval) * a'.lower.eval := by ac_rfl
      _ < (b.upper.eval * a.lower.eval) * a'.lower.eval :=
          (Nat.mul_lt_mul_right (multiset_eval_pos_order a'.lower)).mpr h
      _ = (b.upper.eval * a'.lower.eval) * a.lower.eval := by ac_rfl)

/-- Equivalent left representatives give equivalent strict-order statements. -/
theorem lt_same_left {a a' b : PrimeRatio} (ha : Same a a') :
    Lt a b ↔ Lt a' b :=
  ⟨lt_of_same_left ha, lt_of_same_left (same_symm ha)⟩

/-- Replacing the right argument by an equivalent ratio preserves strict order. -/
private theorem lt_of_same_right {a b b' : PrimeRatio}
    (hb : Same b b') (h : Lt a b) : Lt a b' := by
  unfold Same at hb
  unfold Lt at h ⊢
  exact (Nat.mul_lt_mul_right (multiset_eval_pos_order b.lower)).mp (by
    calc
      (a.upper.eval * b'.lower.eval) * b.lower.eval
          = (a.upper.eval * b.lower.eval) * b'.lower.eval := by ac_rfl
      _ < (b.upper.eval * a.lower.eval) * b'.lower.eval :=
          (Nat.mul_lt_mul_right (multiset_eval_pos_order b'.lower)).mpr h
      _ = (b.upper.eval * b'.lower.eval) * a.lower.eval := by ac_rfl
      _ = (b'.upper.eval * b.lower.eval) * a.lower.eval := by rw [hb]
      _ = (b'.upper.eval * a.lower.eval) * b.lower.eval := by ac_rfl)

/-- Equivalent right representatives give equivalent strict-order statements. -/
theorem lt_same_right {a b b' : PrimeRatio} (hb : Same b b') :
    Lt a b ↔ Lt a b' :=
  ⟨lt_of_same_right hb, lt_of_same_right (same_symm hb)⟩

/-- Strict order is well-defined in both quotient arguments. -/
theorem lt_iff_of_same {a a' b b' : PrimeRatio}
    (ha : Same a a') (hb : Same b b') :
    Lt a b ↔ Lt a' b' :=
  (lt_same_left ha).trans (lt_same_right hb)

/-- Native strict order on positive ratios is irreflexive. -/
theorem lt_irrefl_ratio (a : PrimeRatio) : ¬ Lt a a := by
  unfold Lt
  exact Nat.lt_irrefl _

/-- Native strict order on positive ratios is transitive. -/
theorem lt_trans_ratio {a b c : PrimeRatio}
    (hab : Lt a b) (hbc : Lt b c) : Lt a c := by
  unfold Lt at hab hbc ⊢
  exact (Nat.mul_lt_mul_right (multiset_eval_pos_order b.lower)).mp (by
    calc
      (a.upper.eval * c.lower.eval) * b.lower.eval
          = (a.upper.eval * b.lower.eval) * c.lower.eval := by ac_rfl
      _ < (b.upper.eval * a.lower.eval) * c.lower.eval :=
          (Nat.mul_lt_mul_right (multiset_eval_pos_order c.lower)).mpr hab
      _ = (b.upper.eval * c.lower.eval) * a.lower.eval := by ac_rfl
      _ < (c.upper.eval * b.lower.eval) * a.lower.eval :=
          (Nat.mul_lt_mul_right (multiset_eval_pos_order a.lower)).mpr hbc
      _ = (c.upper.eval * a.lower.eval) * b.lower.eval := by ac_rfl)

end PrimeRatio

namespace MulRat

/-- Strict order lifted from cross-product comparison. -/
def lt (a b : MulRat) : Prop :=
  Quotient.liftOn₂ a b
    PrimeRatio.Lt
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      change PrimeRatio.Same a₁ a₂ at ha
      change PrimeRatio.Same b₁ b₂ at hb
      apply propext
      exact PrimeRatio.lt_iff_of_same ha hb)

instance : LT MulRat := ⟨lt⟩

theorem lt_irrefl (a : MulRat) : ¬ a < a := by
  refine Quotient.inductionOn a ?_
  intro x
  change ¬ PrimeRatio.Lt x x
  exact PrimeRatio.lt_irrefl_ratio x

theorem lt_trans {a b c : MulRat} (hab : a < b) (hbc : b < c) : a < c := by
  refine Quotient.inductionOn a ?_ hab
  intro x hab'
  refine Quotient.inductionOn b ?_ hab' hbc
  intro y hxy hyc
  refine Quotient.inductionOn c ?_ hyc
  intro z hyz
  change PrimeRatio.Lt x z
  exact PrimeRatio.lt_trans_ratio hxy hyz

/-- Multiplicative quotient inside the positive carrier. -/
def ratio (a b : MulRat) : MulRat := a * b⁻¹

@[simp] theorem ratio_self (a : MulRat) : ratio a a = 1 := by
  unfold ratio
  exact mul_inv a

/--
`a` and `b` lie in the same multiplicative `δ`-annulus.

There is no additive distance.  Both orientations of the ratio must remain
strictly below `δ`.
-/
def Within (δ a b : MulRat) : Prop :=
  ratio a b < δ ∧ ratio b a < δ

theorem within_refl {δ a : MulRat} (hδ : 1 < δ) : Within δ a a := by
  simpa [Within] using And.intro hδ hδ

theorem within_symm {δ a b : MulRat} :
    Within δ a b → Within δ b a := by
  intro h
  exact ⟨h.2, h.1⟩

end MulRat
end PrimeTensor
