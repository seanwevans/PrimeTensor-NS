import PrimeTensor.Bridge.Bag.ClosedForm
import PrimeTensor.Bridge.Kernel.Descent

/-!
# Semantic realization after descent to prime multisets

`Bridge.BagClosedForm` proves that the concrete dyadic prime-pair construction
converges to the expected logarithmic product target on every ordered pair of
`PrimeBag`s.

`KernelDescent` quotients those ordered factor chains by represented positive
natural magnitude, producing

    PrimePairApprox.multisetKernel : MultisetStreamCouplingSeed.

This file proves that the conventional semantic target descends through that
quotient as well.  No new analytic estimate is required: quotient induction
reduces the theorem directly to `bagPair_convergesReal_logProduct`.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The concrete multiset-valued stream kernel converges conventionally to the
closed logarithmic product target determined only by the represented positive
natural magnitudes.
-/
theorem multisetKernel_convergesReal_logProduct
    (a b : PrimeMultiset) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (multisetKernel.realize a b)
      (
        Real.exp
          (
            Real.log (a.eval : ℝ) *
              Real.log (b.eval : ℝ)
          )
      ) := by

  refine Quotient.inductionOn a ?_
  intro x

  refine Quotient.inductionOn b ?_
  intro y

  change
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (kernel.bagPair x y)
      (
        Real.exp
          (
            Real.log (x.eval : ℝ) *
              Real.log (y.eval : ℝ)
          )
      )

  exact bagPair_convergesReal_logProduct x y

/--
The same semantic theorem stated for the canonical UFD descent directly from
the prime-pair seed.
-/
theorem kernel_toMultisetCanonical_convergesReal_logProduct
    (a b : PrimeMultiset) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      ((kernel.toMultisetCanonical).realize a b)
      (
        Real.exp
          (
            Real.log (a.eval : ℝ) *
              Real.log (b.eval : ℝ)
          )
      ) := by

  exact multisetKernel_convergesReal_logProduct a b

end PrimePairApprox
end Bridge
end PrimeTensor
