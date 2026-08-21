import PrimeTensor.Prime

/-!
# Oriented prime-multiset ratios

A finite positive rational magnitude is two prime multisets.  Inversion exchanges
orientations; signed exponents are unnecessary.
-/

namespace PrimeTensor

structure PrimeRatio where
  upper : PrimeMultiset
  lower : PrimeMultiset

namespace PrimeRatio

def one : PrimeRatio := ⟨1, 1⟩

def mul (a b : PrimeRatio) : PrimeRatio :=
  ⟨a.upper * b.upper, a.lower * b.lower⟩

def inv (a : PrimeRatio) : PrimeRatio := ⟨a.lower, a.upper⟩

def ratio (a b : PrimeRatio) : PrimeRatio := mul a (inv b)

instance : One PrimeRatio := ⟨one⟩
instance : Mul PrimeRatio := ⟨mul⟩
instance : Inv PrimeRatio := ⟨inv⟩

/-- Equality by positive cross-product, with no subtraction. -/
def Same (a b : PrimeRatio) : Prop :=
  a.upper.eval * b.lower.eval = b.upper.eval * a.lower.eval

/-- Strict order by positive cross-product, with no subtraction. -/
def Lt (a b : PrimeRatio) : Prop :=
  a.upper.eval * b.lower.eval < b.upper.eval * a.lower.eval

instance : LT PrimeRatio := ⟨Lt⟩

/-- Multiplicative annulus membership. -/
def Within (δ a b : PrimeRatio) : Prop :=
  ratio a b < δ ∧ ratio b a < δ

@[simp] theorem upper_mul (a b : PrimeRatio) :
    (a * b).upper.eval = a.upper.eval * b.upper.eval := by
  change PrimeMultiset.eval (a.upper * b.upper) =
    PrimeMultiset.eval a.upper * PrimeMultiset.eval b.upper
  exact PrimeMultiset.eval_mul a.upper b.upper

@[simp] theorem lower_mul (a b : PrimeRatio) :
    (a * b).lower.eval = a.lower.eval * b.lower.eval := by
  change PrimeMultiset.eval (a.lower * b.lower) =
    PrimeMultiset.eval a.lower * PrimeMultiset.eval b.lower
  exact PrimeMultiset.eval_mul a.lower b.lower

@[simp] theorem inv_upper (a : PrimeRatio) : (a⁻¹).upper = a.lower := rfl
@[simp] theorem inv_lower (a : PrimeRatio) : (a⁻¹).lower = a.upper := rfl

end PrimeRatio

end PrimeTensor
