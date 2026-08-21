import PrimeTensor.Scale

/-!
# Composition laws for intrinsic multiplicative scale

This file proves the key refinement law needed by the Cauchy completion:

if `a` is close to `b` at one finer scale and `b` is close to `c` at one
finer scale, then `a` is close to `c` at the current scale.

The proof stays in the prime-barcode carrier.  Its only inequality arithmetic
is on the natural cross-products underlying `PrimeRatio`.
-/

namespace PrimeTensor
namespace MulRat

/-- Left inverse law, derived from commutativity and the existing right inverse. -/
@[simp] theorem inv_mul (a : MulRat) : a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv a

/-- Ratios compose through an intermediate magnitude. -/
theorem ratio_comp (a b c : MulRat) :
    ratio a c = ratio a b * ratio b c := by
  unfold ratio
  symm
  calc
    (a * b⁻¹) * (b * c⁻¹)
        = ((a * b⁻¹) * b) * c⁻¹ := (mul_assoc (a * b⁻¹) b c⁻¹).symm
    _ = (a * (b⁻¹ * b)) * c⁻¹ := by
      rw [mul_assoc a b⁻¹ b]
    _ = (a * 1) * c⁻¹ := by
      rw [inv_mul b]
    _ = a * c⁻¹ := by
      rw [mul_one]

/-- A square of a product can be regrouped into the product of squares. -/
private theorem mul_mul_shuffle (x y : MulRat) :
    (x * y) * (x * y) = (x * x) * (y * y) := by
  calc
    (x * y) * (x * y)
        = x * (y * (x * y)) := mul_assoc x y (x * y)
    _ = x * ((y * x) * y) := by
      rw [← mul_assoc y x y]
    _ = x * ((x * y) * y) := by
      rw [mul_comm y x]
    _ = (x * (x * y)) * y := (mul_assoc x (x * y) y).symm
    _ = ((x * x) * y) * y := by
      rw [← mul_assoc x x y]
    _ = (x * x) * (y * y) := mul_assoc (x * x) y y

/-- Repeated squaring distributes over multiplication. -/
theorem scalePow_mul (x y : MulRat) :
    ∀ level : Depth,
      scalePow (x * y) level = scalePow x level * scalePow y level
  | .one => rfl
  | .succ level => by
      change
        scalePow (x * y) level * scalePow (x * y) level =
          (scalePow x level * scalePow x level) *
            (scalePow y level * scalePow y level)
      rw [scalePow_mul x y level]
      exact mul_mul_shuffle (scalePow x level) (scalePow y level)

/-- Every prime multiset represents a strictly positive natural magnitude. -/
private theorem multiset_eval_pos (q : PrimeMultiset) : 0 < q.eval := by
  refine Quotient.inductionOn q ?_
  intro bag
  exact lt_of_lt_of_le Nat.zero_lt_one (PrimeBag.one_le_eval bag)

@[simp] theorem twoRatio_upper_eval : twoRatio.upper.eval = 2 := by
  norm_num [twoRatio, primeTwo, PrimeMultiset.eval_ofBag,
    PrimeBag.eval_factor, PrimeBag.eval_one]

@[simp] theorem twoRatio_lower_eval : twoRatio.lower.eval = 1 := by
  rfl

/--
If two positive rational magnitudes each have square below `2`, then their
product is below `2`.

This is the native cross-product core of scale composition.
-/
theorem mul_lt_two_of_sq_lt_two {x y : MulRat}
    (hx : x * x < two) (hy : y * y < two) :
    x * y < two := by
  refine Quotient.inductionOn x ?_ hx
  intro xr hxr
  refine Quotient.inductionOn y ?_ hxr hy
  intro yr hxr hyr
  change PrimeRatio.Lt (xr * yr) twoRatio
  change PrimeRatio.Lt (xr * xr) twoRatio at hxr
  change PrimeRatio.Lt (yr * yr) twoRatio at hyr
  unfold PrimeRatio.Lt at hxr hyr ⊢
  simp only [PrimeRatio.upper_mul, PrimeRatio.lower_mul,
    twoRatio_upper_eval, twoRatio_lower_eval, Nat.mul_one] at hxr hyr ⊢

  have hyu : 0 < yr.upper.eval := multiset_eval_pos yr.upper
  have hxl : 0 < xr.lower.eval := multiset_eval_pos xr.lower
  have hyu2 : 0 < yr.upper.eval * yr.upper.eval :=
    Nat.mul_pos hyu hyu
  have hxrBound : 0 < 2 * (xr.lower.eval * xr.lower.eval) :=
    Nat.mul_pos (by norm_num) (Nat.mul_pos hxl hxl)

  apply (Nat.mul_self_lt_mul_self_iff).mp
  calc
    (xr.upper.eval * yr.upper.eval) *
          (xr.upper.eval * yr.upper.eval)
        =
      (xr.upper.eval * xr.upper.eval) *
          (yr.upper.eval * yr.upper.eval) := by ac_rfl
    _ <
      (2 * (xr.lower.eval * xr.lower.eval)) *
          (yr.upper.eval * yr.upper.eval) :=
      (Nat.mul_lt_mul_right hyu2).mpr hxr
    _ =
      (yr.upper.eval * yr.upper.eval) *
          (2 * (xr.lower.eval * xr.lower.eval)) := by ac_rfl
    _ <
      (2 * (yr.lower.eval * yr.lower.eval)) *
          (2 * (xr.lower.eval * xr.lower.eval)) :=
      (Nat.mul_lt_mul_right hxrBound).mpr hyr
    _ =
      (2 * (xr.lower.eval * yr.lower.eval)) *
          (2 * (xr.lower.eval * yr.lower.eval)) := by ac_rfl

/--
One finer scale on each leg composes into the current scale on the endpoints.
-/
theorem scaleWithin_comp {level : Depth} {a b c : MulRat}
    (hab : ScaleWithin (.succ level) a b)
    (hbc : ScaleWithin (.succ level) b c) :
    ScaleWithin level a c := by
  unfold ScaleWithin at hab hbc ⊢

  have habForward :
      scalePow (ratio a b) level * scalePow (ratio a b) level < two := by
    simpa [scalePow] using hab.1

  have hbcForward :
      scalePow (ratio b c) level * scalePow (ratio b c) level < two := by
    simpa [scalePow] using hbc.1

  have hbcBackward :
      scalePow (ratio c b) level * scalePow (ratio c b) level < two := by
    simpa [scalePow] using hbc.2

  have habBackward :
      scalePow (ratio b a) level * scalePow (ratio b a) level < two := by
    simpa [scalePow] using hab.2

  constructor
  · rw [ratio_comp a b c, scalePow_mul]
    exact mul_lt_two_of_sq_lt_two habForward hbcForward
  · rw [ratio_comp c b a, scalePow_mul]
    exact mul_lt_two_of_sq_lt_two hbcBackward habBackward

end MulRat
end PrimeTensor
