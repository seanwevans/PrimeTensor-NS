import PrimeTensor.Bridge.Convergence
import PrimeTensor.Bridge.Cauchy

/-!
# Semantic convergence on ordered prime bags

The prime-pair kernel is extended algebraically in two recursive stages:

1. one prime against every factor in a right `PrimeBag`;
2. every factor in a left `PrimeBag` against the entire right bag.

This file mirrors those two recursions on the conventional real side.

The semantic targets are deliberately kept recursive here.  That makes the
convergence proofs purely structural: atomic convergence is supplied by
`PrimePairStreamSeed.RealizesLogProduct`, while recursive products are handled
by `MulCauchyStream.convergesReal_mul`.

A later bridge file can normalize these recursive targets to the closed form

    exp (log (eval a) * log (eval b)).

Keeping those two steps separate prevents elementary logarithm algebra from
obscuring the actual convergence argument.
-/

namespace PrimeTensor
namespace Bridge

namespace PrimePairStreamSeed

/--
Conventional target obtained by coupling one prime against every factor in a
positive ordered prime bag.
-/
noncomputable def primeAgainstBagTarget
    (p : Prime) :
    PrimeBag → ℝ
  | .one =>
      1
  | .factor q rest =>
      logProductTarget p q *
        primeAgainstBagTarget p rest

/--
Conventional target obtained by coupling every prime in the left ordered bag
against every prime in the right ordered bag.
-/
noncomputable def bagPairTarget :
    PrimeBag → PrimeBag → ℝ
  | .one, _ =>
      1
  | .factor p rest, b =>
      primeAgainstBagTarget p b *
        bagPairTarget rest b

@[simp] theorem primeAgainstBagTarget_one
    (p : Prime) :
    primeAgainstBagTarget p .one = 1 := by
  rfl

@[simp] theorem primeAgainstBagTarget_factor
    (p q : Prime)
    (rest : PrimeBag) :
    primeAgainstBagTarget p (.factor q rest) =
      logProductTarget p q *
        primeAgainstBagTarget p rest := by
  rfl

@[simp] theorem bagPairTarget_one_left
    (b : PrimeBag) :
    bagPairTarget .one b = 1 := by
  rfl

@[simp] theorem bagPairTarget_factor_left
    (p : Prime)
    (rest b : PrimeBag) :
    bagPairTarget (.factor p rest) b =
      primeAgainstBagTarget p b *
        bagPairTarget rest b := by
  rfl

/-- Every one-prime-against-bag semantic target is strictly positive. -/
theorem primeAgainstBagTarget_pos
    (p : Prime) :
    ∀ b : PrimeBag,
      0 < primeAgainstBagTarget p b
  | .one => by
      norm_num
  | .factor q rest => by
      exact
        mul_pos
          (logProductTarget_pos p q)
          (primeAgainstBagTarget_pos p rest)

/-- Every bag-pair semantic target is strictly positive. -/
theorem bagPairTarget_pos :
    ∀ a b : PrimeBag,
      0 < bagPairTarget a b
  | .one, b => by
      norm_num
  | .factor p rest, b => by
      exact
        mul_pos
          (primeAgainstBagTarget_pos p b)
          (bagPairTarget_pos rest b)

/--
Atomic semantic realization propagates through the right-bag recursion.
-/
theorem primeAgainstBag_convergesReal
    (K : PrimeTensor.PrimePairStreamSeed)
    (hK : PrimeTensor.Bridge.PrimePairStreamSeed.RealizesLogProduct K)
    (p : Prime) :
    ∀ b : PrimeBag,
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (K.primeAgainstBag p b)
        (primeAgainstBagTarget p b)
  | .one => by

      change
        PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
          (PrimeTensor.MulCauchyStream.constant 1)
          1

      simpa using
        PrimeTensor.Bridge.MulCauchyStream.convergesReal_constant
          (1 : PrimeTensor.MulRat)

  | .factor q rest => by

      change
        PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
          (
            PrimeTensor.MulCauchyStream.mul
              (K.realize p q)
              (K.primeAgainstBag p rest)
          )
          (
            logProductTarget p q *
              primeAgainstBagTarget p rest
          )

      exact
        PrimeTensor.Bridge.MulCauchyStream.convergesReal_mul
          (hK p q)
          (primeAgainstBag_convergesReal
            K hK p rest)

/--
Atomic semantic realization propagates through the full left-bag recursion.
-/
theorem bagPair_convergesReal
    (K : PrimeTensor.PrimePairStreamSeed)
    (hK : PrimeTensor.Bridge.PrimePairStreamSeed.RealizesLogProduct K) :
    ∀ a b : PrimeBag,
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
        (K.bagPair a b)
        (bagPairTarget a b)
  | .one, b => by

      change
        PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
          (PrimeTensor.MulCauchyStream.constant 1)
          1

      simpa using
        PrimeTensor.Bridge.MulCauchyStream.convergesReal_constant
          (1 : PrimeTensor.MulRat)

  | .factor p rest, b => by

      change
        PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
          (
            PrimeTensor.MulCauchyStream.mul
              (K.primeAgainstBag p b)
              (K.bagPair rest b)
          )
          (
            primeAgainstBagTarget p b *
              bagPairTarget rest b
          )

      exact
        PrimeTensor.Bridge.MulCauchyStream.convergesReal_mul
          (primeAgainstBag_convergesReal
            K hK p b)
          (bagPair_convergesReal
            K hK rest b)

end PrimePairStreamSeed

namespace PrimePairApprox

/--
The concrete dyadic kernel therefore realizes the recursive semantic target on
every ordered pair of prime bags.
-/
theorem bagPair_convergesReal
    (a b : PrimeBag) :
    PrimeTensor.Bridge.MulCauchyStream.ConvergesReal
      (kernel.bagPair a b)
      (
        PrimeTensor.Bridge.PrimePairStreamSeed.bagPairTarget
          a b
      ) := by

  exact
    PrimeTensor.Bridge.PrimePairStreamSeed.bagPair_convergesReal
      kernel
      kernel_realizesLogProduct
      a b

end PrimePairApprox

end Bridge
end PrimeTensor
