import PrimeTensor.Bridge.RatioSemantics
import PrimeTensor.Bridge.KernelStreamFinite

/-!
# Finite semantic realization of the concrete stream kernel

`Bridge.RatioSemantics` proves that the fully oriented canonical stream attached
to two `PrimeRatio` representatives converges to

    exp (ratioLog a * ratioLog b).

This file identifies `ratioLog` with the ordinary logarithm of the conventional
real interpretation of the corresponding `MulRat`, then descends the result
through both quotient inputs.

The endpoint is the finite semantic theorem we wanted:

    (streamFiniteKernel.realize a b).ConvergesReal
      (finiteLogProductTarget a b)

for every finite multiplicative rational pair `a b : MulRat`.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/-- Positive multiset magnitudes remain positive after casting to the reals. -/
private theorem multiset_eval_real_pos
    (a : PrimeMultiset) :
    0 < (a.eval : ℝ) := by

  refine Quotient.inductionOn a ?_
  intro bag

  exact_mod_cast
    (lt_of_lt_of_le
      Nat.zero_lt_one
      (PrimeBag.one_le_eval bag))

/--
The signed log-coordinate of a `PrimeRatio` is exactly the logarithm of the
conventional real value of its canonical `MulRat` quotient representative.
-/
theorem ratioLog_eq_log_ofRatio_toReal
    (a : PrimeRatio) :
    ratioLog a =
      Real.log
        (
          PrimeTensor.Bridge.MulRat.toReal
            (PrimeTensor.MulRat.ofRatio a)
        ) := by

  have hu :
      (a.upper.eval : ℝ) ≠ 0 :=
    ne_of_gt (multiset_eval_real_pos a.upper)

  have hl :
      (a.lower.eval : ℝ) ≠ 0 :=
    ne_of_gt (multiset_eval_real_pos a.lower)

  unfold
    ratioLog
    multisetLog

  have hReal :
      PrimeTensor.Bridge.MulRat.toReal
          (PrimeTensor.MulRat.ofRatio a)
        =
      (a.upper.eval : ℝ) /
        (a.lower.eval : ℝ) := by

    unfold PrimeTensor.Bridge.MulRat.toReal

    have hRat :
        PrimeTensor.Bridge.MulRat.toRat
            (PrimeTensor.MulRat.ofRatio a)
          =
        PrimeTensor.Bridge.PrimeRatio.toRat a := by
      rfl

    rw [hRat]

    unfold PrimeTensor.Bridge.PrimeRatio.toRat

    simp only [
      Rat.cast_div,
      Rat.cast_natCast
    ]

  rw [
    hReal,
    Real.log_div hu hl
  ]

/--
The fully oriented representative stream converges to the already-declared
finite conventional target for the corresponding quotient representatives.
-/
theorem coupleRatioStream_convergesReal_finiteTarget
    (a b : PrimeRatio) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (
        MultisetStreamCouplingSeed.coupleRatioStream
          multisetKernel
          a b
      )
      (
        PrimeTensor.Bridge.finiteLogProductTarget
          (PrimeTensor.MulRat.ofRatio a)
          (PrimeTensor.MulRat.ofRatio b)
      ) := by

  unfold PrimeTensor.Bridge.finiteLogProductTarget

  rw [
    ← ratioLog_eq_log_ofRatio_toReal a,
    ← ratioLog_eq_log_ofRatio_toReal b
  ]

  exact coupleRatioStream_convergesReal a b

/--
The concrete stream-preserving finite kernel realizes the intended conventional
log-product target on every pair of finite multiplicative rationals.
-/
theorem streamFiniteKernel_convergesReal_finiteLogProduct
    (a b : PrimeTensor.MulRat) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (streamFiniteKernel.realize a b)
      (
        PrimeTensor.Bridge.finiteLogProductTarget
          a b
      ) := by

  refine Quotient.inductionOn a ?_
  intro x

  refine Quotient.inductionOn b ?_
  intro y

  change
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (
        MultisetStreamCouplingSeed.coupleRatioStream
          multisetKernel
          x y
      )
      (
        PrimeTensor.Bridge.finiteLogProductTarget
          (PrimeTensor.MulRat.ofRatio x)
          (PrimeTensor.MulRat.ofRatio y)
      )

  exact
    coupleRatioStream_convergesReal_finiteTarget
      x y

end PrimePairApprox
end Bridge
end PrimeTensor
