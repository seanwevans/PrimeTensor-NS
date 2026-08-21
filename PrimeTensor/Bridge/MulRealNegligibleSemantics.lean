import PrimeTensor.Bridge.MulRealScaleSemantics

/-!
# Intrinsic little-o in logarithmic coordinates

This file begins the bridge from the native multiplicative differential germ
to ordinary real first-order semantics.

A fixed completed scale has a genuine boundary asymmetry:

* native `ScaleNear` gives a closed logarithmic bound;
* a strict logarithmic bound gives native `ScaleNear`.

For that reason we do not force a false pointwise iff.  Instead, an intrinsic
`NegligibleRelative` estimate is asked one additional native refinement level
finer.  The extra factor of two converts the closed output bound back into a
strict logarithmic estimate at the requested level.

The resulting theorem is exactly the direction needed to interpret an
intrinsic multiplicative derivative in real logarithmic coordinates.
-/

namespace PrimeTensor
namespace Bridge

/--
Real logarithmic, dyadic-scale little-o.

For every requested positive refinement gain, eventually every strict native
logarithmic scale reached by the base forces the error strictly inside the
correspondingly refined logarithmic radius.
-/
def RealLogScaleLittleO
    (error base : Depth → ℝ) : Prop :=
  ∀ gain : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        ∀ level : Depth,
          abs (base n) <
              PrimeTensor.Bridge.logScaleRadius level →
          abs (error n) <
              PrimeTensor.Bridge.logScaleRadius
                (Depth.advance level gain)

/--
One additional intrinsic refinement converts the closed completed-scale bound
into the strict real logarithmic bound required by `RealLogScaleLittleO`.
-/
theorem logScaleRadius_advance_succ_lt
    (level gain : Depth) :
    PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level (.succ gain))
      <
    PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level gain) := by

  change
    PrimeTensor.Bridge.logScaleRadius
        (.succ (Depth.advance level gain))
      <
    PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level gain)

  rw [
    PrimeTensor.Bridge.logScaleRadius_succ
  ]

  have hPos :
      0 <
        PrimeTensor.Bridge.logScaleRadius
          (Depth.advance level gain) :=
    PrimeTensor.Bridge.logScaleRadius_pos
      (Depth.advance level gain)

  linarith

namespace MulDifferential

/--
Intrinsic negligibility implies strict logarithmic scale-little-o.

The proof deliberately requests `.succ gain` from the native relation.  Native
completion yields only a closed log bound at that finer scale, and the extra
successor makes that closed bound strictly smaller than the originally
requested output radius.
-/
theorem negligibleRelative_to_realLogScaleLittleO
    {error base : PrimeTensor.MulReal.Seq}
    (hNeg :
      PrimeTensor.MulDifferential.NegligibleRelative
        error base) :
    PrimeTensor.Bridge.RealLogScaleLittleO
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (error n)
      )
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (base n)
      ) := by

  intro gain

  obtain ⟨anchor, hTail⟩ :=
    hNeg (.succ gain)

  refine ⟨anchor, ?_⟩

  intro n hn level hBaseLog

  have hBaseNear :
      PrimeTensor.MulReal.ScaleNear
        level
        (base n)
        1 := by

    apply
      PrimeTensor.Bridge.MulReal.scaleNear_of_logValue_lt

    simpa only [
      PrimeTensor.Bridge.MulReal.logValue_one,
      sub_zero
    ] using hBaseLog

  have hErrorNear :
      PrimeTensor.MulReal.ScaleNear
        (Depth.advance level (.succ gain))
        (error n)
        1 :=
    hTail n hn level hBaseNear

  have hErrorClosed :=
    PrimeTensor.Bridge.MulReal.scaleNear_logValue_le
        hErrorNear

  have hErrorClosed' :
      abs
          (
            PrimeTensor.Bridge.MulReal.logValue
              (error n)
          )
        <=
      PrimeTensor.Bridge.logScaleRadius
        (Depth.advance level (.succ gain)) := by

    simpa only [
      PrimeTensor.Bridge.MulReal.logValue_one,
      sub_zero
    ] using hErrorClosed

  exact
    lt_of_le_of_lt
      hErrorClosed'
      (
        PrimeTensor.Bridge.logScaleRadius_advance_succ_lt
            level gain
      )

/--
The logarithmic coordinate of a multiplicative response ratio is the ordinary
difference of output logarithms.
-/
theorem logValue_response
    (f : PrimeTensor.MulReal → PrimeTensor.MulReal)
    (x : PrimeTensor.MulReal)
    (h : PrimeTensor.MulReal.Seq)
    (n : Depth) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulDifferential.response
            f x h n
        )
      =
    PrimeTensor.Bridge.MulReal.logValue
        (f (x * h n)) -
      PrimeTensor.Bridge.MulReal.logValue
        (f x) := by

  unfold PrimeTensor.MulDifferential.response

  exact
    PrimeTensor.Bridge.MulReal.logValue_ratio
      (f (x * h n))
      (f x)

/--
The logarithmic coordinate of the first-order multiplicative error ratio is
the ordinary difference between the actual and model logarithmic responses.
-/
theorem logValue_firstOrderError
    (actual model : PrimeTensor.MulReal.Seq)
    (n : Depth) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ratio
            (actual n)
            (model n)
        )
      =
    PrimeTensor.Bridge.MulReal.logValue
        (actual n) -
      PrimeTensor.Bridge.MulReal.logValue
        (model n) := by

  exact
    PrimeTensor.Bridge.MulReal.logValue_ratio
      (actual n)
      (model n)

/--
Every native first-order equivalence therefore induces a strict real
logarithmic scale-little-o estimate on its error coordinate.
-/
theorem firstOrderEquivalent_to_realLogScaleLittleO
    {base actual model : PrimeTensor.MulReal.Seq}
    (hFirst :
      PrimeTensor.MulDifferential.FirstOrderEquivalent
        base actual model) :
    PrimeTensor.Bridge.RealLogScaleLittleO
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (
              PrimeTensor.MulReal.ratio
                (actual n)
                (model n)
            )
      )
      (
        fun n =>
          PrimeTensor.Bridge.MulReal.logValue
            (base n)
      ) := by

  exact
    PrimeTensor.Bridge.MulDifferential.negligibleRelative_to_realLogScaleLittleO
        hFirst

end MulDifferential

end Bridge
end PrimeTensor
