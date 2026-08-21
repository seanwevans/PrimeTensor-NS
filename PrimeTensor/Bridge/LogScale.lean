import PrimeTensor.Bridge.Scale
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-coordinate semantics of intrinsic scale

This is a bridge-only theorem layer.

The native intrinsic scale is defined by repeated squaring of multiplicative
ratios below the ruler `2`.  On strictly positive conventional real values,
that condition is exactly an ordinary bound on the difference of logarithmic
coordinates.

We define a bridge scale factor

    1, 2, 4, 8, ...

indexed by the native positive `Depth`, and the corresponding log radius

    log 2,
    log 2 / 2,
    log 2 / 4,
    ...

Then

    MulRat.ScaleWithin level a b

is equivalent to

    |log (toReal a) - log (toReal b)| < logScaleRadius level.

No logarithm or additive metric is introduced into the native object language.
-/

namespace PrimeTensor
namespace Bridge

/--
The real exponent represented by native repeated squaring at a given positive
depth.
-/
def logScaleFactor : Depth → ℝ
  | .one => 1
  | .succ d =>
      2 * logScaleFactor d

@[simp] theorem logScaleFactor_one :
    logScaleFactor .one = 1 := by
  rfl

@[simp] theorem logScaleFactor_succ
    (d : Depth) :
    logScaleFactor (.succ d) =
      2 * logScaleFactor d := by
  rfl

theorem logScaleFactor_pos :
    ∀ d : Depth,
      0 < logScaleFactor d
  | .one => by
      norm_num
  | .succ d => by
      rw [logScaleFactor_succ]
      exact mul_pos (by norm_num)
        (logScaleFactor_pos d)

/--
Conventional logarithmic radius corresponding to one native intrinsic scale.
Each successor halves the previous radius.
-/
noncomputable def logScaleRadius
    (d : Depth) : ℝ :=
  Real.log 2 / logScaleFactor d

theorem logScaleRadius_pos
    (d : Depth) :
    0 < logScaleRadius d := by

  unfold logScaleRadius

  exact div_pos
    (Real.log_pos (by norm_num))
    (logScaleFactor_pos d)

@[simp] theorem logScaleRadius_one :
    logScaleRadius .one =
      Real.log 2 := by

  unfold logScaleRadius

  rw [logScaleFactor_one]

  simp

theorem logScaleRadius_succ
    (d : Depth) :
    logScaleRadius (.succ d) =
      logScaleRadius d / 2 := by

  unfold logScaleRadius

  rw [logScaleFactor_succ]

  field_simp

/-- Repeated real squaring preserves strict positivity. -/
theorem logScale_realScalePow_pos
    {x : ℝ}
    (hx : 0 < x) :
    ∀ d : Depth,
      0 < realScalePow x d
  | .one => hx
  | .succ d => by
      change
        0 <
          realScalePow x d *
            realScalePow x d

      exact mul_pos
        (logScale_realScalePow_pos hx d)
        (logScale_realScalePow_pos hx d)

/--
The logarithm of repeated squaring is multiplication by the bridge scale
factor.
-/
theorem log_realScalePow
    {x : ℝ}
    (hx : 0 < x) :
    ∀ d : Depth,
      Real.log (realScalePow x d) =
        Real.log x * logScaleFactor d

  | .one => by
      simp only [
        realScalePow,
        logScaleFactor_one,
        mul_one
      ]

  | .succ d => by
      change
        Real.log
            (
              realScalePow x d *
                realScalePow x d
            )
          =
        Real.log x *
          (2 * logScaleFactor d)

      have hq :
          realScalePow x d ≠ 0 :=
        ne_of_gt (logScale_realScalePow_pos hx d)

      rw [
        Real.log_mul hq hq,
        log_realScalePow hx d
      ]

      ring

/--
Repeated squaring below the ruler `2` is equivalent to the corresponding
one-sided logarithmic radius bound.
-/
theorem realScalePow_lt_two_iff_log_lt
    {x : ℝ}
    (hx : 0 < x)
    (d : Depth) :
    realScalePow x d < 2 ↔
      Real.log x < logScaleRadius d := by

  have hpow :
      0 < realScalePow x d :=
    logScale_realScalePow_pos hx d

  have htwo :
      (0 : ℝ) < 2 := by
    norm_num

  rw [
    ← Real.log_lt_log_iff hpow htwo,
    log_realScalePow hx d
  ]

  unfold logScaleRadius

  have hf :
      0 < logScaleFactor d :=
    logScaleFactor_pos d

  exact
    (lt_div_iff₀ hf).symm

/--
Exact bridge characterization of native scale closeness in logarithmic
coordinates.
-/
theorem MulRat.scaleWithin_iff_log
    (level : Depth)
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.MulRat.ScaleWithin level a b ↔
      abs
        (
          Real.log
              (PrimeTensor.Bridge.MulRat.toReal a) -
            Real.log
              (PrimeTensor.Bridge.MulRat.toReal b)
        )
        <
      logScaleRadius level := by

  have ha :
      0 <
        PrimeTensor.Bridge.MulRat.toReal a :=
    PrimeTensor.Bridge.MulRat.toReal_pos a

  have hb :
      0 <
        PrimeTensor.Bridge.MulRat.toReal b :=
    PrimeTensor.Bridge.MulRat.toReal_pos b

  have hab :
      0 <
        PrimeTensor.Bridge.MulRat.toReal a /
          PrimeTensor.Bridge.MulRat.toReal b :=
    div_pos ha hb

  have hba :
      0 <
        PrimeTensor.Bridge.MulRat.toReal b /
          PrimeTensor.Bridge.MulRat.toReal a :=
    div_pos hb ha

  rw [
    PrimeTensor.Bridge.MulRat.scaleWithin_iff_real,
    realScalePow_lt_two_iff_log_lt hab level,
    realScalePow_lt_two_iff_log_lt hba level
  ]

  have hane :
      PrimeTensor.Bridge.MulRat.toReal a ≠ 0 :=
    ne_of_gt ha

  have hbne :
      PrimeTensor.Bridge.MulRat.toReal b ≠ 0 :=
    ne_of_gt hb

  rw [
    Real.log_div hane hbne,
    Real.log_div hbne hane,
    abs_lt
  ]

  constructor

  · intro h

    constructor

    · have hneg :=
        neg_lt_neg h.2

      simpa only [
        neg_sub
      ] using hneg

    · exact h.1

  · intro h

    constructor

    · exact h.2

    · have hneg :=
        neg_lt_neg h.1

      simpa only [
        neg_sub,
        neg_neg
      ] using hneg

end Bridge
end PrimeTensor
