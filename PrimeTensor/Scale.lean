import PrimeTensor.Order

/-!
# Intrinsic dyadic multiplicative scale

Instead of quantifying over arbitrary rational tolerances, this file uses one
fixed multiplicative ruler, `two`, and refines scale by repeated squaring.

At level `one`, a ratio is close when it is below `two`.
At each successor level, the ratio is squared once more before comparison.

Thus scale depth is intrinsic and positive-indexed:
  r < 2,
  r*r < 2,
  (r*r)*(r*r) < 2,
  ...

No additive midpoint, rational square root, or zeroth scale is part of the
object language.
-/

namespace PrimeTensor
namespace MulRat

/-- The prime barcode representing the rational magnitude `2`. -/
def twoRatio : PrimeRatio :=
  ⟨PrimeMultiset.ofBag (.factor primeTwo .one), 1⟩

/-- Distinguished multiplicative ruler. -/
def two : MulRat :=
  ofRatio twoRatio

/-- The pivot is strictly below the ruler. -/
theorem one_lt_two : (1 : MulRat) < two := by
  change PrimeRatio.Lt (1 : PrimeRatio) twoRatio
  unfold PrimeRatio.Lt twoRatio
  simp only [PrimeRatio.one_upper, PrimeRatio.one_lower,
    PrimeMultiset.eval_one, PrimeMultiset.eval_ofBag,
    PrimeBag.eval_factor, PrimeBag.eval_one]
  norm_num [primeTwo]

/--
Repeated squaring indexed by positive depth.

`scalePow r .one = r`, and every successor squares the previous scale value.
Hence the effective exponents are `1, 2, 4, 8, ...`.
-/
def scalePow (r : MulRat) : Depth → MulRat
  | .one => r
  | .succ d =>
      let q := scalePow r d
      q * q

@[simp] theorem scalePow_one : ∀ d : Depth, scalePow (1 : MulRat) d = 1
  | .one => rfl
  | .succ d => by
      change scalePow (1 : MulRat) d * scalePow (1 : MulRat) d = 1
      rw [scalePow_one d, one_mul]

/--
Two magnitudes are close at a given intrinsic scale when both oriented ratios,
after the scale's repeated squaring, remain below `two`.
-/
def ScaleWithin (level : Depth) (a b : MulRat) : Prop :=
  scalePow (ratio a b) level < two ∧
  scalePow (ratio b a) level < two

theorem scaleWithin_refl (level : Depth) (a : MulRat) :
    ScaleWithin level a a := by
  change scalePow (ratio a a) level < two ∧
    scalePow (ratio a a) level < two
  constructor
  · rw [ratio_self, scalePow_one]
    exact one_lt_two
  · rw [ratio_self, scalePow_one]
    exact one_lt_two

theorem scaleWithin_symm {level : Depth} {a b : MulRat} :
    ScaleWithin level a b → ScaleWithin level b a := by
  intro h
  exact ⟨h.2, h.1⟩

end MulRat
end PrimeTensor
