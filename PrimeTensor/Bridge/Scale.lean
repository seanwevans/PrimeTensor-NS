import PrimeTensor.Bridge.Approx
import Mathlib.Data.Rat.Cast.Order

/-!
# Conventional semantics of intrinsic multiplicative scale

This file is a bridge theorem layer only.

It proves that the native strict order on `MulRat` agrees with ordinary strict
order after conventional interpretation, that native ratio becomes ordinary
division, and that native repeated squaring becomes repeated real squaring.

Consequently `MulRat.ScaleWithin` has an exact conventional interpretation as
two repeated-square inequalities below the real ruler `2`.

No conventional order or real operation is added to the native carrier.
-/

namespace PrimeTensor
namespace Bridge

private theorem scale_multiset_eval_pos
    (q : PrimeMultiset) :
    0 < q.eval := by
  refine Quotient.inductionOn q ?_
  intro b
  exact lt_of_lt_of_le
    Nat.zero_lt_one
    (PrimeBag.one_le_eval b)

/--
Strict order on oriented prime-ratio representatives is exactly strict order
of their conventional rational values.
-/
theorem PrimeRatio.lt_iff_toRat_lt
    (a b : PrimeRatio) :
    PrimeRatio.Lt a b ↔
      PrimeTensor.Bridge.PrimeRatio.toRat a <
        PrimeTensor.Bridge.PrimeRatio.toRat b := by

  unfold PrimeRatio.Lt
  unfold PrimeTensor.Bridge.PrimeRatio.toRat

  have ha :
      0 < (a.lower.eval : ℚ) := by
    exact_mod_cast scale_multiset_eval_pos a.lower

  have hb :
      0 < (b.lower.eval : ℚ) := by
    exact_mod_cast scale_multiset_eval_pos b.lower

  rw [div_lt_div_iff₀ ha hb]

  norm_cast

/--
The quotient-level native strict order agrees exactly with conventional
rational order.
-/
theorem MulRat.lt_iff_toRat_lt
    (a b : PrimeTensor.MulRat) :
    a < b ↔
      PrimeTensor.Bridge.MulRat.toRat a <
        PrimeTensor.Bridge.MulRat.toRat b := by

  refine Quotient.inductionOn₂ a b ?_
  intro x y

  change
    PrimeRatio.Lt x y ↔
      PrimeTensor.Bridge.PrimeRatio.toRat x <
        PrimeTensor.Bridge.PrimeRatio.toRat y

  exact
    PrimeTensor.Bridge.PrimeRatio.lt_iff_toRat_lt
      x y

/--
The native strict order also agrees exactly with conventional real order.
-/
theorem MulRat.lt_iff_toReal_lt
    (a b : PrimeTensor.MulRat) :
    a < b ↔
      PrimeTensor.Bridge.MulRat.toReal a <
        PrimeTensor.Bridge.MulRat.toReal b := by

  rw [PrimeTensor.Bridge.MulRat.lt_iff_toRat_lt]

  unfold PrimeTensor.Bridge.MulRat.toReal

  exact
    (Rat.cast_lt
      (K := ℝ)
      (p := PrimeTensor.Bridge.MulRat.toRat a)
      (q := PrimeTensor.Bridge.MulRat.toRat b)).symm

/-- The distinguished native ruler `two` interprets conventionally as `2`. -/
@[simp] theorem MulRat.toReal_two :
    PrimeTensor.Bridge.MulRat.toReal
        PrimeTensor.MulRat.two =
      (2 : ℝ) := by

  unfold PrimeTensor.Bridge.MulRat.toReal
  unfold PrimeTensor.Bridge.MulRat.toRat
  unfold PrimeTensor.MulRat.two
  unfold PrimeTensor.MulRat.ofRatio
  change
    ((PrimeTensor.Bridge.PrimeRatio.toRat
        PrimeTensor.MulRat.twoRatio : ℚ) : ℝ) =
      (2 : ℝ)
  unfold PrimeTensor.MulRat.twoRatio
  unfold PrimeTensor.Bridge.PrimeRatio.toRat
  norm_num [
    PrimeMultiset.eval_ofBag,
    PrimeBag.eval_factor,
    PrimeBag.eval_one,
    PrimeMultiset.eval_one,
    primeTwo
  ]

/-- Native multiplicative ratio becomes ordinary positive real division. -/
@[simp] theorem MulRat.toReal_ratio
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulRat.toReal
        (PrimeTensor.MulRat.ratio a b) =
      PrimeTensor.Bridge.MulRat.toReal a /
        PrimeTensor.Bridge.MulRat.toReal b := by

  unfold PrimeTensor.MulRat.ratio

  rw [
    PrimeTensor.Bridge.MulRat.toReal_mul,
    PrimeTensor.Bridge.MulRat.toReal_inv
  ]

  exact div_eq_mul_inv _ _

/--
Conventional repeated squaring indexed by the same positive native `Depth`.
This definition exists only in the bridge.
-/
def realScalePow
    (x : ℝ) :
    Depth → ℝ
  | .one => x
  | .succ d =>
      let q := realScalePow x d
      q * q

@[simp] theorem realScalePow_one :
    ∀ d : Depth,
      realScalePow 1 d = 1
  | .one => rfl
  | .succ d => by
      change
        realScalePow 1 d *
            realScalePow 1 d =
          1
      rw [realScalePow_one d]
      norm_num

/--
Conventional interpretation commutes exactly with native repeated squaring.
-/
theorem MulRat.toReal_scalePow
    (r : PrimeTensor.MulRat) :
    ∀ level : Depth,
      PrimeTensor.Bridge.MulRat.toReal
          (PrimeTensor.MulRat.scalePow r level) =
        realScalePow
          (PrimeTensor.Bridge.MulRat.toReal r)
          level
  | .one => rfl
  | .succ level => by
      change
        PrimeTensor.Bridge.MulRat.toReal
            (
              PrimeTensor.MulRat.scalePow r level *
                PrimeTensor.MulRat.scalePow r level
            ) =
          realScalePow
              (PrimeTensor.Bridge.MulRat.toReal r)
              level *
            realScalePow
              (PrimeTensor.Bridge.MulRat.toReal r)
              level

      rw [
        PrimeTensor.Bridge.MulRat.toReal_mul,
        MulRat.toReal_scalePow r level
      ]

/--
Exact conventional meaning of native intrinsic scale closeness.
-/
theorem MulRat.scaleWithin_iff_real
    (level : Depth)
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.MulRat.ScaleWithin level a b ↔
      realScalePow
          (
            PrimeTensor.Bridge.MulRat.toReal a /
              PrimeTensor.Bridge.MulRat.toReal b
          )
          level <
        2 ∧
      realScalePow
          (
            PrimeTensor.Bridge.MulRat.toReal b /
              PrimeTensor.Bridge.MulRat.toReal a
          )
          level <
        2 := by

  unfold PrimeTensor.MulRat.ScaleWithin

  constructor

  · intro h
    constructor

    · have hreal :=
        (
          PrimeTensor.Bridge.MulRat.lt_iff_toReal_lt
            (PrimeTensor.MulRat.scalePow
              (PrimeTensor.MulRat.ratio a b)
              level)
            PrimeTensor.MulRat.two
        ).mp h.1

      simpa only [
        PrimeTensor.Bridge.MulRat.toReal_scalePow,
        PrimeTensor.Bridge.MulRat.toReal_ratio,
        PrimeTensor.Bridge.MulRat.toReal_two
      ] using hreal

    · have hreal :=
        (
          PrimeTensor.Bridge.MulRat.lt_iff_toReal_lt
            (PrimeTensor.MulRat.scalePow
              (PrimeTensor.MulRat.ratio b a)
              level)
            PrimeTensor.MulRat.two
        ).mp h.2

      simpa only [
        PrimeTensor.Bridge.MulRat.toReal_scalePow,
        PrimeTensor.Bridge.MulRat.toReal_ratio,
        PrimeTensor.Bridge.MulRat.toReal_two
      ] using hreal

  · intro h
    constructor

    · apply
        (
          PrimeTensor.Bridge.MulRat.lt_iff_toReal_lt
            (PrimeTensor.MulRat.scalePow
              (PrimeTensor.MulRat.ratio a b)
              level)
            PrimeTensor.MulRat.two
        ).mpr

      simpa only [
        PrimeTensor.Bridge.MulRat.toReal_scalePow,
        PrimeTensor.Bridge.MulRat.toReal_ratio,
        PrimeTensor.Bridge.MulRat.toReal_two
      ] using h.1

    · apply
        (
          PrimeTensor.Bridge.MulRat.lt_iff_toReal_lt
            (PrimeTensor.MulRat.scalePow
              (PrimeTensor.MulRat.ratio b a)
              level)
            PrimeTensor.MulRat.two
        ).mpr

      simpa only [
        PrimeTensor.Bridge.MulRat.toReal_scalePow,
        PrimeTensor.Bridge.MulRat.toReal_ratio,
        PrimeTensor.Bridge.MulRat.toReal_two
      ] using h.2

end Bridge
end PrimeTensor
