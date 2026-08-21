import PrimeTensor.Bridge.MulRealLogAlgebra

/-!
# Faithfulness of the completed logarithmic coordinate

`MulReal.logValue` is already known to respect the completed multiplicative
algebra.  This file proves that it also separates completed points.

The key statement is stream-level:

    equal logarithmic limits
      => intrinsic asymptotic equivalence.

At any requested intrinsic scale, take one successor-finer logarithmic radius.
Each stream is eventually within that half-radius of the common real limit, so
their mutual log distance is strictly inside the requested radius.  The exact
bridge theorem `scaleWithin_iff_log` then returns intrinsic `ScaleWithin`.

Consequently

    logValue a = logValue b  <->  a = b.

Thus the completed multiplicative carrier embeds faithfully into ordinary real
logarithmic coordinate space.
-/

namespace PrimeTensor
namespace Bridge

namespace MulCauchyStream

/--
Equal canonical logarithmic limits force intrinsic asymptotic equivalence of
Cauchy stream representatives.
-/
theorem asymptotic_of_logLimit_eq
    {a b : PrimeTensor.MulCauchyStream}
    (hLimit :
      PrimeTensor.Bridge.MulCauchyStream.logLimit a =
        PrimeTensor.Bridge.MulCauchyStream.logLimit b) :
    PrimeTensor.MulAsymptotic a b := by

  intro level

  have hFinePos :
      0 <
        PrimeTensor.Bridge.logScaleRadius
          (.succ level) :=
    PrimeTensor.Bridge.logScaleRadius_pos
      (.succ level)

  obtain ⟨aAnchor, hA⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      a
      (PrimeTensor.Bridge.logScaleRadius
        (.succ level))
      hFinePos

  obtain ⟨bAnchor, hB⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      b
      (PrimeTensor.Bridge.logScaleRadius
        (.succ level))
      hFinePos

  let anchor : Depth :=
    Depth.join aAnchor bAnchor

  refine ⟨anchor, ?_⟩

  intro n hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hn

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hn

  have hANear :=
    hA n hnA

  have hBNearRaw :=
    hB n hnB

  have hBNear :
      abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a -
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n
        )
        <
      PrimeTensor.Bridge.logScaleRadius
        (.succ level) := by

    rw [
      hLimit,
      abs_sub_comm
    ]

    exact hBNearRaw

  apply
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
        level
        (a.term n)
        (b.term n)
    ).2

  calc
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n
        )
        ≤
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
          ) +
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          ) :=
      abs_sub_le _ _ _

    _ <
      PrimeTensor.Bridge.logScaleRadius (.succ level) +
        PrimeTensor.Bridge.logScaleRadius (.succ level) :=
      add_lt_add hANear hBNear

    _ =
      PrimeTensor.Bridge.logScaleRadius level := by
      rw [
        PrimeTensor.Bridge.logScaleRadius_succ
      ]
      ring

/--
Two intrinsic Cauchy streams are asymptotic exactly when their canonical
logarithmic limits agree.
-/
theorem asymptotic_iff_logLimit_eq
    {a b : PrimeTensor.MulCauchyStream} :
    PrimeTensor.MulAsymptotic a b ↔
      PrimeTensor.Bridge.MulCauchyStream.logLimit a =
        PrimeTensor.Bridge.MulCauchyStream.logLimit b := by

  constructor

  · exact
      PrimeTensor.Bridge.MulCauchyStream.logLimit_eq_of_asymptotic

  · exact
      PrimeTensor.Bridge.MulCauchyStream.asymptotic_of_logLimit_eq

end MulCauchyStream

namespace MulReal

/--
The completed logarithmic coordinate is injective.
-/
theorem logValue_injective :
    Function.Injective
      PrimeTensor.Bridge.MulReal.logValue := by

  intro a b h

  refine Quotient.inductionOn₂ a b ?_ h

  intro sa sb hLog

  apply
    PrimeTensor.MulReal.ofStream_eq_of_asymptotic

  apply
    PrimeTensor.Bridge.MulCauchyStream.asymptotic_of_logLimit_eq

  change
    PrimeTensor.Bridge.MulCauchyStream.logLimit sa =
      PrimeTensor.Bridge.MulCauchyStream.logLimit sb
    at hLog

  exact hLog

/--
Equality of completed multiplicative reals is exactly equality of their
canonical logarithmic coordinates.
-/
theorem logValue_eq_iff
    {a b : PrimeTensor.MulReal} :
    PrimeTensor.Bridge.MulReal.logValue a =
        PrimeTensor.Bridge.MulReal.logValue b
      ↔
    a = b := by

  constructor

  · intro h
    exact
      PrimeTensor.Bridge.MulReal.logValue_injective h

  · intro h
    rw [h]

end MulReal

end Bridge
end PrimeTensor
