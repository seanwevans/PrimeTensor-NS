import PrimeTensor.Bridge.KernelSemantics

/-!
# Additive logarithmic semantics of completed multiplicative reals

`MulReal.logValue` is now defined on the full intrinsic completion.  This file
proves that it is the expected logarithmic coordinate:

    logValue 1        = 0
    logValue (a * b)  = logValue a + logValue b
    logValue a⁻¹      = - logValue a
    logValue (a / b)  = logValue a - logValue b

All additive, subtractive, negative, and zero-valued statements remain
strictly inside the conventional `Bridge` layer.

Together with `logProductCoupling_logValue`, this gives the completed
coordinate algebra

    L(ab)   = L(a) + L(b)
    L(C(a,b)) = L(a) * L(b),

so the intrinsic multiplicative carrier becomes additive in logarithmic
coordinates while the completed coupling becomes bilinear.
-/

namespace PrimeTensor
namespace Bridge

namespace MulCauchyStream

@[simp]
theorem logTerm_mul
    (a b : PrimeTensor.MulCauchyStream)
    (n : Depth) :
    PrimeTensor.Bridge.MulCauchyStream.logTerm
        (PrimeTensor.MulCauchyStream.mul a b)
        n
      =
    PrimeTensor.Bridge.MulCauchyStream.logTerm a n +
      PrimeTensor.Bridge.MulCauchyStream.logTerm b n := by

  unfold PrimeTensor.Bridge.MulCauchyStream.logTerm

  rw [
    PrimeTensor.MulCauchyStream.mul_term,
    PrimeTensor.Bridge.MulRat.toReal_mul
  ]

  have ha :
      PrimeTensor.Bridge.MulRat.toReal (a.term n) ≠ 0 :=
    ne_of_gt
      (PrimeTensor.Bridge.MulRat.toReal_pos (a.term n))

  have hb :
      PrimeTensor.Bridge.MulRat.toReal (b.term n) ≠ 0 :=
    ne_of_gt
      (PrimeTensor.Bridge.MulRat.toReal_pos (b.term n))

  exact Real.log_mul ha hb

@[simp]
theorem logTerm_inv
    (a : PrimeTensor.MulCauchyStream)
    (n : Depth) :
    PrimeTensor.Bridge.MulCauchyStream.logTerm
        (PrimeTensor.MulCauchyStream.inv a)
        n
      =
    -
      PrimeTensor.Bridge.MulCauchyStream.logTerm a n := by

  unfold PrimeTensor.Bridge.MulCauchyStream.logTerm

  rw [
    PrimeTensor.MulCauchyStream.inv_term,
    PrimeTensor.Bridge.MulRat.toReal_inv,
    Real.log_inv
  ]

@[simp]
theorem logTerm_constant
    (q : PrimeTensor.MulRat)
    (n : Depth) :
    PrimeTensor.Bridge.MulCauchyStream.logTerm
        (PrimeTensor.MulCauchyStream.constant q)
        n
      =
    Real.log
      (PrimeTensor.Bridge.MulRat.toReal q) := by

  unfold PrimeTensor.Bridge.MulCauchyStream.logTerm

  rw [PrimeTensor.MulCauchyStream.constant_term]

/--
The chosen logarithmic limit of a pointwise stream product is the sum of the
chosen logarithmic limits.
-/
theorem logLimit_mul
    (a b : PrimeTensor.MulCauchyStream) :
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.mul a b)
      =
    PrimeTensor.Bridge.MulCauchyStream.logLimit a +
      PrimeTensor.Bridge.MulCauchyStream.logLimit b := by

  have ha :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm a)
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
            )
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        a
        (PrimeTensor.Bridge.MulCauchyStream.logLimit a)
    ).mp
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          a
      )

  have hb :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm b)
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
            )
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        b
        (PrimeTensor.Bridge.MulCauchyStream.logLimit b)
    ).mp
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          b
      )

  have hSum :=
    ha.add hb

  have hMul :
      Filter.Tendsto
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            (PrimeTensor.MulCauchyStream.mul a b)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a +
                PrimeTensor.Bridge.MulCauchyStream.logLimit b
            )
        ) := by

    have hFun :
        PrimeTensor.Bridge.MulCauchyStream.logTerm
            (PrimeTensor.MulCauchyStream.mul a b)
          =
        fun n =>
          PrimeTensor.Bridge.MulCauchyStream.logTerm a n +
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n := by
      funext n
      exact
        PrimeTensor.Bridge.MulCauchyStream.logTerm_mul
          a b n

    rw [hFun]

    exact hSum

  have hConv :
      PrimeTensor.Bridge.MulCauchyStream.LogConverges
        (PrimeTensor.MulCauchyStream.mul a b)
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a +
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        (PrimeTensor.MulCauchyStream.mul a b)
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a +
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        )
    ).mpr hMul

  exact
    PrimeTensor.Bridge.MulCauchyStream.logConverges_unique
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          (PrimeTensor.MulCauchyStream.mul a b)
      )
      hConv

/--
The chosen logarithmic limit of a pointwise inverse is the negative of the
chosen logarithmic limit.
-/
theorem logLimit_inv
    (a : PrimeTensor.MulCauchyStream) :
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.inv a)
      =
    -
      PrimeTensor.Bridge.MulCauchyStream.logLimit a := by

  have ha :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm a)
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
            )
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        a
        (PrimeTensor.Bridge.MulCauchyStream.logLimit a)
    ).mp
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          a
      )

  have hNeg :=
    ha.neg

  have hInv :
      Filter.Tendsto
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            (PrimeTensor.MulCauchyStream.inv a)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              -
                PrimeTensor.Bridge.MulCauchyStream.logLimit a
            )
        ) := by

    have hFun :
        PrimeTensor.Bridge.MulCauchyStream.logTerm
            (PrimeTensor.MulCauchyStream.inv a)
          =
        fun n =>
          -
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n := by
      funext n
      exact
        PrimeTensor.Bridge.MulCauchyStream.logTerm_inv
          a n

    rw [hFun]

    exact hNeg

  have hConv :
      PrimeTensor.Bridge.MulCauchyStream.LogConverges
        (PrimeTensor.MulCauchyStream.inv a)
        (
          -
            PrimeTensor.Bridge.MulCauchyStream.logLimit a
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        (PrimeTensor.MulCauchyStream.inv a)
        (
          -
            PrimeTensor.Bridge.MulCauchyStream.logLimit a
        )
    ).mpr hInv

  exact
    PrimeTensor.Bridge.MulCauchyStream.logConverges_unique
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          (PrimeTensor.MulCauchyStream.inv a)
      )
      hConv

/--
A constant finite stream has the expected constant logarithmic limit.
-/
theorem logLimit_constant
    (q : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.constant q)
      =
    Real.log
      (PrimeTensor.Bridge.MulRat.toReal q) := by

  have hConv :
      PrimeTensor.Bridge.MulCauchyStream.LogConverges
        (PrimeTensor.MulCauchyStream.constant q)
        (
          Real.log
            (PrimeTensor.Bridge.MulRat.toReal q)
        ) := by

    intro ε hε

    refine ⟨.one, ?_⟩

    intro n hn

    simpa only [
      PrimeTensor.Bridge.MulCauchyStream.logTerm_constant,
      sub_self,
      abs_zero
    ] using hε

  exact
    PrimeTensor.Bridge.MulCauchyStream.logConverges_unique
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          (PrimeTensor.MulCauchyStream.constant q)
      )
      hConv

end MulCauchyStream

namespace MulReal

/-- Finite barcodes embed with their ordinary real logarithm. -/
@[simp]
theorem logValue_ofRat
    (q : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulReal.logValue
        (PrimeTensor.MulReal.ofRat q)
      =
    Real.log
      (PrimeTensor.Bridge.MulRat.toReal q) := by

  change
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.constant q)
      =
    Real.log
      (PrimeTensor.Bridge.MulRat.toReal q)

  exact
    PrimeTensor.Bridge.MulCauchyStream.logLimit_constant
      q

/-- The intrinsic multiplicative pivot is additive zero in log coordinates. -/
@[simp]
theorem logValue_one :
    PrimeTensor.Bridge.MulReal.logValue
        (1 : PrimeTensor.MulReal)
      =
    0 := by

  rw [
    ← PrimeTensor.MulReal.ofRat_one,
    PrimeTensor.Bridge.MulReal.logValue_ofRat,
    PrimeTensor.Bridge.MulRat.toReal_one,
    Real.log_one
  ]

/-- Intrinsic multiplication becomes ordinary addition in log coordinates. -/
@[simp]
theorem logValue_mul
    (a b : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue (a * b)
      =
    PrimeTensor.Bridge.MulReal.logValue a +
      PrimeTensor.Bridge.MulReal.logValue b := by

  refine Quotient.inductionOn₂ a b ?_

  intro sa sb

  change
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.mul sa sb)
      =
    PrimeTensor.Bridge.MulCauchyStream.logLimit sa +
      PrimeTensor.Bridge.MulCauchyStream.logLimit sb

  exact
    PrimeTensor.Bridge.MulCauchyStream.logLimit_mul
      sa sb

/-- Intrinsic inversion becomes ordinary negation in log coordinates. -/
@[simp]
theorem logValue_inv
    (a : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue a⁻¹
      =
    -
      PrimeTensor.Bridge.MulReal.logValue a := by

  refine Quotient.inductionOn a ?_

  intro sa

  change
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (PrimeTensor.MulCauchyStream.inv sa)
      =
    -
      PrimeTensor.Bridge.MulCauchyStream.logLimit sa

  exact
    PrimeTensor.Bridge.MulCauchyStream.logLimit_inv
      sa

/-- Intrinsic ratio becomes ordinary subtraction in log coordinates. -/
@[simp]
theorem logValue_ratio
    (a b : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (PrimeTensor.MulReal.ratio a b)
      =
    PrimeTensor.Bridge.MulReal.logValue a -
      PrimeTensor.Bridge.MulReal.logValue b := by

  unfold PrimeTensor.MulReal.ratio

  rw [
    PrimeTensor.Bridge.MulReal.logValue_mul,
    PrimeTensor.Bridge.MulReal.logValue_inv
  ]

  ring

end MulReal

namespace PrimePairApprox

/--
The completed coupling is literally bilinear multiplication in the canonical
logarithmic coordinate.
-/
theorem logProductCoupling_logBilinear
    (a b : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (logProductCoupling.couple a b)
      =
    PrimeTensor.Bridge.MulReal.logValue a *
      PrimeTensor.Bridge.MulReal.logValue b := by

  exact logProductCoupling_logValue a b

end PrimePairApprox

end Bridge
end PrimeTensor
