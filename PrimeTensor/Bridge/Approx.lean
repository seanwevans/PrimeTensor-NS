import PrimeTensor.Bridge.Encode
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Dyadic prime-pair approximants

This bridge module constructs the first concrete candidate for the nonlinear
prime-pair kernel.

For prime atoms `p,q` and positive native `Depth d`, let

    T(p,q) = exp (log p * log q)

and choose a positive dyadic denominator

    D(d) = 2 ^ precision(d),

where native depth `.one` receives precision `1`.

The finite native barcode at stage `d` is

    floor (T(p,q) * D(d)) / D(d).

Because `T(p,q) > 1`, the numerator is always positive.  Hence every stage can
be reverse-encoded as an actual `MulRat` with no zero numerator and no fallback
case.

This file proves the conventional bridge error estimate

    0 <= T - Q_d < 1 / D(d).

The next layer will translate this quantitative estimate into native
`MulRat.ScaleWithin` Cauchy control.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
Positive numerical precision attached to native positive `Depth`.
This conversion exists only in the bridge.
-/
def precision : Depth → ℕ
  | .one => 1
  | .succ d => Nat.succ (precision d)

theorem precision_pos :
    ∀ d : Depth, 0 < precision d
  | .one => by
      norm_num [precision]
  | .succ d => by
      change 0 < Nat.succ (precision d)
      exact Nat.succ_pos _

/-- Positive dyadic denominator at one native depth. -/
def denom (d : Depth) : ℕ :=
  2 ^ precision d

theorem denom_pos
    (d : Depth) :
    0 < denom d := by
  unfold denom
  positivity

theorem denom_ne_zero
    (d : Depth) :
    denom d ≠ 0 :=
  Nat.ne_of_gt (denom_pos d)

/-- Prime-pair semantic target already fixed by `Bridge.Real`. -/
noncomputable def target
    (p q : Prime) : ℝ :=
  PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget p q

theorem target_pos
    (p q : Prime) :
    0 < target p q := by
  unfold target
  exact
    PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget_pos
      p q

/-- For genuine prime atoms the logarithmic-product target is strictly above 1. -/
theorem one_lt_target
    (p q : Prime) :
    1 < target p q := by

  unfold target
  unfold
    PrimeTensor.Bridge.PrimePairStreamSeed.logProductTarget

  have hp :
      (1 : ℝ) < (p.value : ℝ) := by
    exact_mod_cast p.one_lt

  have hq :
      (1 : ℝ) < (q.value : ℝ) := by
    exact_mod_cast q.one_lt

  have hlp :
      0 < Real.log (p.value : ℝ) :=
    Real.log_pos hp

  have hlq :
      0 < Real.log (q.value : ℝ) :=
    Real.log_pos hq

  have hprod :
      0 <
        Real.log (p.value : ℝ) *
          Real.log (q.value : ℝ) :=
    mul_pos hlp hlq

  exact Real.one_lt_exp_iff.mpr hprod

/-- Real-scaled target whose natural floor becomes the dyadic numerator. -/
noncomputable def scaled
    (p q : Prime)
    (d : Depth) : ℝ :=
  target p q * (denom d : ℝ)

/-- Natural numerator of the lower dyadic approximant. -/
noncomputable def numerator
    (p q : Prime)
    (d : Depth) : ℕ :=
  ⌊scaled p q d⌋₊

theorem one_le_scaled
    (p q : Prime)
    (d : Depth) :
    1 ≤ scaled p q d := by

  unfold scaled

  have ht :
      (1 : ℝ) ≤ target p q :=
    le_of_lt (one_lt_target p q)

  have hdNat :
      1 ≤ denom d :=
    Nat.one_le_iff_ne_zero.mpr (denom_ne_zero d)

  have hd :
      (1 : ℝ) ≤ (denom d : ℝ) := by
    exact_mod_cast hdNat

  calc
    (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ target p q * 1 :=
      mul_le_mul_of_nonneg_right ht (by norm_num)
    _ ≤ target p q * (denom d : ℝ) :=
      mul_le_mul_of_nonneg_left hd (le_of_lt (target_pos p q))

/-- The lower-dyadic numerator is never zero. -/
theorem numerator_pos
    (p q : Prime)
    (d : Depth) :
    0 < numerator p q d := by

  have hone :
      1 ≤ numerator p q d := by
    unfold numerator
    exact
      (Nat.one_le_floor_iff (scaled p q d)).mpr
        (one_le_scaled p q d)

  exact lt_of_lt_of_le Nat.zero_lt_one hone

theorem numerator_ne_zero
    (p q : Prime)
    (d : Depth) :
    numerator p q d ≠ 0 :=
  Nat.ne_of_gt (numerator_pos p q d)

/--
Concrete native finite barcode approximating the prime-pair target at depth
`d`.
-/
noncomputable def term
    (p q : Prime)
    (d : Depth) :
    PrimeTensor.MulRat :=
  PrimeTensor.Bridge.Encode.ratio
    (numerator p q d)
    (denom d)
    (numerator_ne_zero p q d)
    (denom_ne_zero d)

/-- Conventional real value of the native stage term. -/
theorem term_toReal
    (p q : Prime)
    (d : Depth) :
    PrimeTensor.Bridge.MulRat.toReal
        (term p q d) =
      (numerator p q d : ℝ) /
        (denom d : ℝ) := by

  unfold term
  exact
    PrimeTensor.Bridge.Encode.ratio_toReal
      (numerator p q d)
      (denom d)
      (numerator_ne_zero p q d)
      (denom_ne_zero d)

/-- Real denominator is strictly positive. -/
theorem denom_real_pos
    (d : Depth) :
    0 < (denom d : ℝ) := by
  exact_mod_cast denom_pos d

/--
The native stage is a lower approximation to the semantic target.
-/
theorem term_le_target
    (p q : Prime)
    (d : Depth) :
    PrimeTensor.Bridge.MulRat.toReal
        (term p q d) ≤
      target p q := by

  rw [term_toReal]

  have hscaled_nonneg :
      0 ≤ scaled p q d :=
    le_of_lt <|
      mul_pos
        (target_pos p q)
        (denom_real_pos d)

  have hfloor :
      (numerator p q d : ℝ) ≤
        scaled p q d := by
    unfold numerator
    exact Nat.floor_le hscaled_nonneg

  unfold scaled at hfloor

  exact
    (div_le_iff₀ (denom_real_pos d)).mpr
      hfloor

/--
The semantic target lies less than one dyadic unit above the native stage.
-/
theorem target_lt_term_add_unit
    (p q : Prime)
    (d : Depth) :
    target p q <
      PrimeTensor.Bridge.MulRat.toReal
          (term p q d) +
        1 / (denom d : ℝ) := by

  rw [term_toReal]

  have hfloor :
      scaled p q d <
        (numerator p q d : ℝ) + 1 := by
    unfold numerator
    exact Nat.lt_floor_add_one (scaled p q d)

  unfold scaled at hfloor

  have hdiv :
      target p q <
        ((numerator p q d : ℝ) + 1) /
          (denom d : ℝ) := by
    exact
      (lt_div_iff₀ (denom_real_pos d)).mpr
        hfloor

  have hsplit :
      ((numerator p q d : ℝ) + 1) /
          (denom d : ℝ) =
        (numerator p q d : ℝ) /
            (denom d : ℝ) +
          1 / (denom d : ℝ) := by
    ring

  rw [hsplit] at hdiv
  exact hdiv

/-- Nonnegative signed error of the lower dyadic approximation. -/
theorem error_nonneg
    (p q : Prime)
    (d : Depth) :
    0 ≤
      target p q -
        PrimeTensor.Bridge.MulRat.toReal
          (term p q d) := by
  exact sub_nonneg.mpr (term_le_target p q d)

/-- Quantitative dyadic error bound. -/
theorem error_lt_unit
    (p q : Prime)
    (d : Depth) :
    target p q -
        PrimeTensor.Bridge.MulRat.toReal
          (term p q d) <
      1 / (denom d : ℝ) := by

  have h :=
    target_lt_term_add_unit p q d

  linarith

/-- Absolute error has the same dyadic bound. -/
theorem abs_error_lt_unit
    (p q : Prime)
    (d : Depth) :
    abs
        (
          PrimeTensor.Bridge.MulRat.toReal
              (term p q d) -
            target p q
        ) <
      1 / (denom d : ℝ) := by

  have hnonneg :=
    error_nonneg p q d

  have hlt :=
    error_lt_unit p q d

  rw [abs_sub_comm]
  rw [abs_of_nonneg hnonneg]
  exact hlt

/-- The concrete candidate before its native Cauchy proof is packaged. -/
noncomputable def stream
    (p q : Prime) :
    PrimeTensor.MulStream :=
  fun d => term p q d

end PrimePairApprox
end Bridge
end PrimeTensor
