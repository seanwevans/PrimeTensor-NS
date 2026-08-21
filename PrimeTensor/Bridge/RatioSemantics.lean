import PrimeTensor.Bridge.MultisetSemantics
import PrimeTensor.Fluid.CouplingStreamFinite

/-!
# Semantic realization on oriented prime ratios

The positive-multiset kernel now has a closed conventional target.  This file
pushes that target through the two stream-level orientation steps used by
`CouplingStreamFinite`.

For a positive multiset define its bridge log-coordinate by

    multisetLog a = log (a.eval).

For an oriented `PrimeRatio` define

    ratioLog a = multisetLog a.upper - multisetLog a.lower.

The first orientation produces

    exp (ratioLog a * multisetLog b),

and orienting the second slot produces

    exp (ratioLog a * ratioLog b).

No new approximation estimate appears here.  The only analytic input is the
already-proved convergence of the positive multiset kernel plus closure of
`ConvergesReal` under stream ratio.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/-- Conventional additive log-coordinate of a positive prime multiset. -/
noncomputable def multisetLog
    (a : PrimeMultiset) : ℝ :=
  Real.log (a.eval : ℝ)

/-- Conventional signed log-coordinate of an oriented prime ratio. -/
noncomputable def ratioLog
    (a : PrimeRatio) : ℝ :=
  multisetLog a.upper -
    multisetLog a.lower

/-- The positive multiset coordinate is just notation for the closed target. -/
theorem multisetKernel_convergesReal_multisetLog
    (a b : PrimeMultiset) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (multisetKernel.realize a b)
      (
        Real.exp
          (
            multisetLog a *
              multisetLog b
          )
      ) := by

  exact
    multisetKernel_convergesReal_logProduct
      a b

/--
Orienting the first input converts the positive log-coordinate into the signed
ratio log-coordinate.
-/
theorem orientedLeftStream_convergesReal
    (a : PrimeRatio)
    (b : PrimeMultiset) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (
        MultisetStreamCouplingSeed.orientedLeftStream
          multisetKernel
          a b
      )
      (
        Real.exp
          (
            ratioLog a *
              multisetLog b
          )
      ) := by

  have hUpper :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (multisetKernel.realize a.upper b)
        (
          Real.exp
            (
              multisetLog a.upper *
                multisetLog b
            )
        ) :=
    multisetKernel_convergesReal_multisetLog
      a.upper b

  have hLower :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (multisetKernel.realize a.lower b)
        (
          Real.exp
            (
              multisetLog a.lower *
                multisetLog b
            )
        ) :=
    multisetKernel_convergesReal_multisetLog
      a.lower b

  have hRatio :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (
          PrimeTensor.MulCauchyStream.mul
            (multisetKernel.realize a.upper b)
            (
              PrimeTensor.MulCauchyStream.inv
                (multisetKernel.realize a.lower b)
            )
        )
        (
          Real.exp
              (
                multisetLog a.upper *
                  multisetLog b
              ) /
            Real.exp
              (
                multisetLog a.lower *
                  multisetLog b
              )
        ) := by

    exact
      PrimeTensor.Bridge.MulCauchyStream.convergesReal_ratio
        hUpper
        hLower
        (Real.exp_ne_zero _)

  have hTarget :
      Real.exp
            (
              multisetLog a.upper *
                multisetLog b
            ) /
          Real.exp
            (
              multisetLog a.lower *
                multisetLog b
            )
        =
      Real.exp
        (
          ratioLog a *
            multisetLog b
        ) := by

    rw [← Real.exp_sub]

    congr 1

    unfold ratioLog

    ring

  unfold
    MultisetStreamCouplingSeed.orientedLeftStream
    MulCauchyStream.ratio

  rw [← hTarget]

  exact hRatio

/--
After orienting the second input as well, the canonical finite representative
has exactly the bilinear logarithmic target.
-/
theorem coupleRatioStream_convergesReal
    (a b : PrimeRatio) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (
        MultisetStreamCouplingSeed.coupleRatioStream
          multisetKernel
          a b
      )
      (
        Real.exp
          (
            ratioLog a *
              ratioLog b
          )
      ) := by

  have hUpper :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (
          MultisetStreamCouplingSeed.orientedLeftStream
            multisetKernel
            a b.upper
        )
        (
          Real.exp
            (
              ratioLog a *
                multisetLog b.upper
            )
        ) :=
    orientedLeftStream_convergesReal
      a b.upper

  have hLower :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (
          MultisetStreamCouplingSeed.orientedLeftStream
            multisetKernel
            a b.lower
        )
        (
          Real.exp
            (
              ratioLog a *
                multisetLog b.lower
            )
        ) :=
    orientedLeftStream_convergesReal
      a b.lower

  have hRatio :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (
          PrimeTensor.MulCauchyStream.mul
            (
              MultisetStreamCouplingSeed.orientedLeftStream
                multisetKernel
                a b.upper
            )
            (
              PrimeTensor.MulCauchyStream.inv
                (
                  MultisetStreamCouplingSeed.orientedLeftStream
                    multisetKernel
                    a b.lower
                )
            )
        )
        (
          Real.exp
              (
                ratioLog a *
                  multisetLog b.upper
              ) /
            Real.exp
              (
                ratioLog a *
                  multisetLog b.lower
              )
        ) := by

    exact
      PrimeTensor.Bridge.MulCauchyStream.convergesReal_ratio
        hUpper
        hLower
        (Real.exp_ne_zero _)

  have hTarget :
      Real.exp
            (
              ratioLog a *
                multisetLog b.upper
            ) /
          Real.exp
            (
              ratioLog a *
                multisetLog b.lower
            )
        =
      Real.exp
        (
          ratioLog a *
            ratioLog b
        ) := by

    rw [← Real.exp_sub]

    congr 1

    unfold ratioLog

    ring

  unfold
    MultisetStreamCouplingSeed.coupleRatioStream
    MulCauchyStream.ratio

  rw [← hTarget]

  exact hRatio

end PrimePairApprox
end Bridge
end PrimeTensor
