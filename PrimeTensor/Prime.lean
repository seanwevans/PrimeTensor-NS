import PrimeTensor.Depth

/-!
# Prime atoms, prime bags, and prime multisets

`PrimeBag` is an ordered factor chain whose terminator is the
multiplicative pivot `one`.

`PrimeMultiset` quotients factor chains by equality of their represented
natural magnitude.  By unique prime factorization this removes factor order,
so commutativity becomes equality in the public representation.
-/

namespace PrimeTensor

structure Prime where
  value : ℕ
  prime : Nat.Prime value

namespace Prime

@[simp] theorem one_lt (p : Prime) : 1 < p.value := p.prime.one_lt

end Prime

/-- Ordered factor-chain representation underneath the quotient. -/
inductive PrimeBag where
  | one : PrimeBag
  | factor : Prime → PrimeBag → PrimeBag

namespace PrimeBag

/-- Natural-number interpretation of a finite prime barcode. -/
def eval : PrimeBag → ℕ
  | .one => 1
  | .factor p rest => p.value * rest.eval

@[simp] theorem eval_one : eval .one = 1 := rfl

@[simp] theorem eval_factor (p : Prime) (r : PrimeBag) :
    eval (.factor p r) = p.value * eval r := rfl

/-- Every finite prime barcode lies on or above the multiplicative pivot. -/
theorem one_le_eval : ∀ b : PrimeBag, 1 ≤ b.eval
  | .one => by rfl
  | .factor p rest => by
      have hp : 1 ≤ p.value := Nat.le_of_lt p.one_lt
      have hr : 1 ≤ rest.eval := one_le_eval rest
      exact Nat.mul_le_mul hp hr

/-- Multiplication is factor-chain concatenation. -/
def mul : PrimeBag → PrimeBag → PrimeBag
  | .one, b => b
  | .factor p rest, b => .factor p (mul rest b)

instance : One PrimeBag := ⟨.one⟩
instance : Mul PrimeBag := ⟨mul⟩

@[simp] theorem one_mul (b : PrimeBag) : (1 : PrimeBag) * b = b := rfl

@[simp] theorem mul_one : ∀ b : PrimeBag, b * 1 = b
  | .one => rfl
  | .factor p rest => by
      change PrimeBag.factor p (rest * 1) = PrimeBag.factor p rest
      exact congrArg (PrimeBag.factor p) (mul_one rest)

theorem mul_assoc : ∀ a b c : PrimeBag, (a * b) * c = a * (b * c)
  | .one, _, _ => rfl
  | .factor p rest, b, c => by
      change PrimeBag.factor p ((rest * b) * c) =
        PrimeBag.factor p (rest * (b * c))
      exact congrArg (PrimeBag.factor p) (mul_assoc rest b c)

@[simp] theorem eval_mul : ∀ a b : PrimeBag,
    eval (a * b) = eval a * eval b
  | .one, b => by
      change eval b = 1 * eval b
      exact (Nat.one_mul (eval b)).symm
  | .factor p rest, b => by
      change p.value * eval (rest * b) =
        (p.value * eval rest) * eval b
      rw [eval_mul rest b]
      exact (Nat.mul_assoc p.value (eval rest) (eval b)).symm

/-- Factor order is irrelevant at the public boundary. -/
def Same (a b : PrimeBag) : Prop := a.eval = b.eval

@[refl] theorem same_refl (a : PrimeBag) : Same a a := rfl

@[symm] theorem same_symm {a b : PrimeBag} : Same a b → Same b a := Eq.symm

@[trans] theorem same_trans {a b c : PrimeBag} :
    Same a b → Same b c → Same a c := Eq.trans

/-- The explicit setoid used by `PrimeMultiset`. -/
def setoid : Setoid PrimeBag where
  r := Same
  iseqv := ⟨same_refl, @same_symm, @same_trans⟩

/-- Concatenating two bags commutes modulo `Same`. -/
theorem mul_comm_same (a b : PrimeBag) : Same (a * b) (b * a) := by
  unfold Same
  rw [eval_mul, eval_mul, Nat.mul_comm]

/-- Multiplication respects `Same` in both arguments. -/
theorem mul_same {a₁ a₂ b₁ b₂ : PrimeBag}
    (ha : Same a₁ a₂) (hb : Same b₁ b₂) :
    Same (a₁ * b₁) (a₂ * b₂) := by
  unfold Same at ha hb ⊢
  rw [eval_mul, eval_mul, ha, hb]

end PrimeBag

/-- Prime factor chains modulo represented magnitude. -/
abbrev PrimeMultiset := Quotient PrimeBag.setoid

namespace PrimeMultiset

/-- Inject a factor chain into the quotient, with the setoid supplied explicitly. -/
def ofBag (b : PrimeBag) : PrimeMultiset :=
  Quotient.mk PrimeBag.setoid b

/-- Multiplicative pivot. -/
def one : PrimeMultiset := ofBag 1

/-- Natural-number interpretation of the quotient. -/
def eval (q : PrimeMultiset) : ℕ :=
  Quotient.liftOn q PrimeBag.eval (by
    intro a b h
    change PrimeBag.Same a b at h
    exact h)

/-- Quotient multiplication induced by concatenation. -/
def mul (a b : PrimeMultiset) : PrimeMultiset :=
  Quotient.liftOn₂ a b
    (fun x y => ofBag (x * y))
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      change PrimeBag.Same a₁ a₂ at ha
      change PrimeBag.Same b₁ b₂ at hb
      change Quotient.mk PrimeBag.setoid (a₁ * b₁) =
        Quotient.mk PrimeBag.setoid (a₂ * b₂)
      apply Quotient.sound
      exact PrimeBag.mul_same ha hb)

instance : One PrimeMultiset := ⟨one⟩
instance : Mul PrimeMultiset := ⟨mul⟩

@[simp] theorem eval_ofBag (b : PrimeBag) : eval (ofBag b) = b.eval := by
  rfl

@[simp] theorem eval_one : eval (1 : PrimeMultiset) = 1 := by
  change PrimeBag.eval PrimeBag.one = 1
  rfl

@[simp] theorem eval_mul (a b : PrimeMultiset) : eval (a * b) = eval a * eval b := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change PrimeBag.eval (x * y) = PrimeBag.eval x * PrimeBag.eval y
  exact PrimeBag.eval_mul x y

/-- Commutativity is actual equality after quotienting factor order. -/
theorem mul_comm (a b : PrimeMultiset) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  change Quotient.mk PrimeBag.setoid (x * y) =
    Quotient.mk PrimeBag.setoid (y * x)
  apply Quotient.sound
  exact PrimeBag.mul_comm_same x y

end PrimeMultiset

/-- Convenient concrete atoms for probes. -/
def primeTwo : Prime := ⟨2, by norm_num⟩
def primeThree : Prime := ⟨3, by norm_num⟩
def primeFive : Prime := ⟨5, by norm_num⟩

/-- `12 = 2·2·3` as an ordered constructor term. -/
def twelveBag : PrimeBag :=
  .factor primeTwo (.factor primeTwo (.factor primeThree .one))

/-- `12` as a prime multiset. -/
def twelve : PrimeMultiset := PrimeMultiset.ofBag twelveBag

end PrimeTensor
