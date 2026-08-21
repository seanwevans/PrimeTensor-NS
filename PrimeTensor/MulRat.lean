import PrimeTensor.Ratio

/-!
# Positive rational prime barcodes modulo cross-product equivalence

`PrimeRatio` is an oriented pair of prime multisets.  It still has many
representatives for the same rational magnitude.  This file quotients those
representatives by cross-product equality before any Cauchy completion is
attempted.

No ordinary rational or real value is stored here.
-/

namespace PrimeTensor
namespace PrimeRatio

/-- Quotient-level prime multisets always evaluate to a positive natural. -/
private theorem multiset_eval_pos (q : PrimeMultiset) : 0 < q.eval := by
  refine Quotient.inductionOn q ?_
  intro b
  exact lt_of_lt_of_le Nat.zero_lt_one (PrimeBag.one_le_eval b)

/-- Cross-product equality is reflexive. -/
@[refl] theorem same_refl (a : PrimeRatio) : Same a a := by
  unfold Same
  rfl

/-- Cross-product equality is symmetric. -/
@[symm] theorem same_symm {a b : PrimeRatio} : Same a b → Same b a := by
  intro h
  exact h.symm

/-- Cross-product equality is transitive, using positivity for cancellation. -/
@[trans] theorem same_trans {a b c : PrimeRatio}
    (hab : Same a b) (hbc : Same b c) : Same a c := by
  unfold Same at hab hbc ⊢
  apply Nat.eq_of_mul_eq_mul_right (multiset_eval_pos b.lower)
  calc
    (a.upper.eval * c.lower.eval) * b.lower.eval
        = (a.upper.eval * b.lower.eval) * c.lower.eval := by ac_rfl
    _ = (b.upper.eval * a.lower.eval) * c.lower.eval := by rw [hab]
    _ = (b.upper.eval * c.lower.eval) * a.lower.eval := by ac_rfl
    _ = (c.upper.eval * b.lower.eval) * a.lower.eval := by rw [hbc]
    _ = (c.upper.eval * a.lower.eval) * b.lower.eval := by ac_rfl

/-- Setoid of finite positive rational prime barcodes. -/
def setoid : Setoid PrimeRatio where
  r := Same
  iseqv := ⟨same_refl, @same_symm, @same_trans⟩

/-- Multiplication respects rational cross-product equivalence. -/
theorem mul_same {a₁ a₂ b₁ b₂ : PrimeRatio}
    (ha : Same a₁ a₂) (hb : Same b₁ b₂) :
    Same (a₁ * b₁) (a₂ * b₂) := by
  unfold Same at ha hb ⊢
  simp only [upper_mul, lower_mul]
  calc
    (a₁.upper.eval * b₁.upper.eval) *
          (a₂.lower.eval * b₂.lower.eval)
        =
      (a₁.upper.eval * a₂.lower.eval) *
          (b₁.upper.eval * b₂.lower.eval) := by ac_rfl
    _ =
      (a₂.upper.eval * a₁.lower.eval) *
          (b₂.upper.eval * b₁.lower.eval) := by rw [ha, hb]
    _ =
      (a₂.upper.eval * b₂.upper.eval) *
          (a₁.lower.eval * b₁.lower.eval) := by ac_rfl

/-- Inversion respects rational cross-product equivalence. -/
theorem inv_same {a b : PrimeRatio} (h : Same a b) :
    Same a⁻¹ b⁻¹ := by
  unfold Same at h ⊢
  simp only [inv_upper, inv_lower]
  calc
    a.lower.eval * b.upper.eval
        = b.upper.eval * a.lower.eval := by ac_rfl
    _ = a.upper.eval * b.lower.eval := h.symm
    _ = b.lower.eval * a.upper.eval := by ac_rfl

@[simp] theorem one_upper : (1 : PrimeRatio).upper = 1 := rfl
@[simp] theorem one_lower : (1 : PrimeRatio).lower = 1 := rfl

theorem one_mul_same (a : PrimeRatio) : Same (1 * a) a := by
  unfold Same
  simp only [upper_mul, lower_mul, one_upper, one_lower,
    PrimeMultiset.eval_one, Nat.one_mul]

theorem mul_one_same (a : PrimeRatio) : Same (a * 1) a := by
  unfold Same
  simp only [upper_mul, lower_mul, one_upper, one_lower,
    PrimeMultiset.eval_one, Nat.mul_one]

theorem mul_assoc_same (a b c : PrimeRatio) :
    Same ((a * b) * c) (a * (b * c)) := by
  unfold Same
  simp only [upper_mul, lower_mul]
  ac_rfl

theorem mul_comm_same (a b : PrimeRatio) :
    Same (a * b) (b * a) := by
  unfold Same
  simp only [upper_mul, lower_mul]
  ac_rfl

theorem inv_inv_same (a : PrimeRatio) : Same (a⁻¹)⁻¹ a := by
  unfold Same
  simp only [inv_upper, inv_lower]

theorem mul_inv_same_one (a : PrimeRatio) : Same (a * a⁻¹) 1 := by
  unfold Same
  simp only [upper_mul, lower_mul, inv_upper, inv_lower,
    one_upper, one_lower, PrimeMultiset.eval_one,
    Nat.mul_one, Nat.one_mul]
  exact Nat.mul_comm _ _

end PrimeRatio

/--
Finite positive rational magnitudes as prime barcodes modulo cross-product
equivalence.
-/
abbrev MulRat := Quotient PrimeRatio.setoid

namespace MulRat

def ofRatio (q : PrimeRatio) : MulRat :=
  Quotient.mk PrimeRatio.setoid q

def one : MulRat := ofRatio 1

def mul (a b : MulRat) : MulRat :=
  Quotient.liftOn₂ a b
    (fun x y => ofRatio (x * y))
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      change PrimeRatio.Same a₁ a₂ at ha
      change PrimeRatio.Same b₁ b₂ at hb
      change Quotient.mk PrimeRatio.setoid (a₁ * b₁) =
        Quotient.mk PrimeRatio.setoid (a₂ * b₂)
      apply Quotient.sound
      exact PrimeRatio.mul_same ha hb)

def inv (a : MulRat) : MulRat :=
  Quotient.liftOn a
    (fun x => ofRatio x⁻¹)
    (by
      intro a b h
      change PrimeRatio.Same a b at h
      change Quotient.mk PrimeRatio.setoid a⁻¹ =
        Quotient.mk PrimeRatio.setoid b⁻¹
      apply Quotient.sound
      exact PrimeRatio.inv_same h)

instance : One MulRat := ⟨one⟩
instance : Mul MulRat := ⟨mul⟩
instance : Inv MulRat := ⟨inv⟩

@[simp] theorem one_mul (a : MulRat) : (1 : MulRat) * a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk PrimeRatio.setoid ((1 : PrimeRatio) * x) =
    Quotient.mk PrimeRatio.setoid x
  apply Quotient.sound
  exact PrimeRatio.one_mul_same x

@[simp] theorem mul_one (a : MulRat) : a * (1 : MulRat) = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk PrimeRatio.setoid (x * (1 : PrimeRatio)) =
    Quotient.mk PrimeRatio.setoid x
  apply Quotient.sound
  exact PrimeRatio.mul_one_same x

theorem mul_assoc (a b c : MulRat) : (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change Quotient.mk PrimeRatio.setoid ((x * y) * z) =
    Quotient.mk PrimeRatio.setoid (x * (y * z))
  apply Quotient.sound
  exact PrimeRatio.mul_assoc_same x y z

theorem mul_comm (a b : MulRat) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change Quotient.mk PrimeRatio.setoid (x * y) =
    Quotient.mk PrimeRatio.setoid (y * x)
  apply Quotient.sound
  exact PrimeRatio.mul_comm_same x y

@[simp] theorem inv_inv (a : MulRat) : (a⁻¹)⁻¹ = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk PrimeRatio.setoid ((x⁻¹)⁻¹) =
    Quotient.mk PrimeRatio.setoid x
  apply Quotient.sound
  exact PrimeRatio.inv_inv_same x

@[simp] theorem mul_inv (a : MulRat) : a * a⁻¹ = 1 := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk PrimeRatio.setoid (x * x⁻¹) =
    Quotient.mk PrimeRatio.setoid (1 : PrimeRatio)
  apply Quotient.sound
  exact PrimeRatio.mul_inv_same_one x

end MulRat
end PrimeTensor
