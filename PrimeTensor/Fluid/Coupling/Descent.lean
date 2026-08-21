import PrimeTensor.Fluid.Coupling.Prime

/-!
# Descent of prime-pair coupling to prime multisets

`CouplingPrime` proves that a stream attached to each pair of prime atoms
determines a termwise-bilinear coupling on ordered `PrimeBag`s.

The only obstruction to passing to the public positive-barcode type
`PrimeMultiset` is unique factorization: two bags with the same represented
natural magnitude must produce the same coupled stream.

This file isolates that exact number-theoretic obligation as `RespectsSame`.
Assuming it, the bag construction descends through the quotient, remains
termwise bilinear, and yields the `BarcodeCouplingSeed` already used by the
finite oriented-ratio layer.

No unique-factorization theorem is assumed silently: `RespectsSame` is the
single explicit hypothesis still to be proved from the prime structure.
-/

namespace PrimeTensor

namespace MulCauchyStream

/-- Two intrinsic Cauchy streams are equal when all of their terms are equal. -/
theorem eq_of_term_eq
    {a b : MulCauchyStream}
    (h : ∀ n : Depth, a.term n = b.term n) :
    a = b := by
  cases a with
  | mk aTerm aCauchy =>
      cases b with
      | mk bTerm bCauchy =>
          change ∀ n : Depth, aTerm n = bTerm n at h
          have hterm : aTerm = bTerm := funext h
          cases hterm
          rfl

end MulCauchyStream

namespace PrimePairStreamSeed

/--
The exact unique-factorization descent obligation.

If either ordered prime factor chain is replaced by another chain representing
the same positive natural magnitude, every stage of the coupled output stream
is unchanged.
-/
structure RespectsSame
    (K : PrimePairStreamSeed) : Prop where

  term_eq :
    ∀ {a a' b b' : PrimeBag},
      PrimeBag.Same a a' →
      PrimeBag.Same b b' →
      ∀ n : Depth,
        (K.bagPair a b).term n =
          (K.bagPair a' b').term n

end PrimePairStreamSeed

/--
Canonical stream-valued coupling on positive prime multisets.
-/
structure MultisetStreamCouplingSeed where
  realize :
    PrimeMultiset → PrimeMultiset → MulCauchyStream

/--
Termwise multiplicative bilinearity for a positive-multiset stream coupling.
-/
structure IsMultisetStreamCouplingSeed
    (C : MultisetStreamCouplingSeed) : Prop where

  one_left :
    ∀ (b : PrimeMultiset) (n : Depth),
      (C.realize 1 b).term n = 1

  one_right :
    ∀ (a : PrimeMultiset) (n : Depth),
      (C.realize a 1).term n = 1

  mul_left :
    ∀ (a b c : PrimeMultiset) (n : Depth),
      (C.realize (a * b) c).term n =
        (C.realize a c).term n *
        (C.realize b c).term n

  mul_right :
    ∀ (a b c : PrimeMultiset) (n : Depth),
      (C.realize a (b * c)).term n =
        (C.realize a b).term n *
        (C.realize a c).term n

namespace PrimePairStreamSeed

/--
Descend the ordered-bag prime-pair construction through `PrimeMultiset`.
-/
def toMultiset
    (K : PrimePairStreamSeed)
    (hSame : K.RespectsSame) :
    MultisetStreamCouplingSeed where

  realize := fun a b =>
    Quotient.liftOn₂ a b
      (fun x y => K.bagPair x y)
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        change PrimeBag.Same a₁ a₂ at ha
        change PrimeBag.Same b₁ b₂ at hb
        apply MulCauchyStream.eq_of_term_eq
        intro n
        exact hSame.term_eq ha hb n)

@[simp] theorem toMultiset_ofBag_term
    (K : PrimePairStreamSeed)
    (hSame : K.RespectsSame)
    (a b : PrimeBag)
    (n : Depth) :
    ((K.toMultiset hSame).realize
        (PrimeMultiset.ofBag a)
        (PrimeMultiset.ofBag b)).term n =
      (K.bagPair a b).term n := rfl

/--
The descended positive-multiset coupling inherits all four termwise bilinear
laws from the bag recursion.
-/
theorem toMultiset_lawful
    (K : PrimePairStreamSeed)
    (hSame : K.RespectsSame) :
    IsMultisetStreamCouplingSeed
      (K.toMultiset hSame) := by

  constructor

  · intro b n
    refine Quotient.inductionOn b ?_
    intro y
    change (K.bagPair .one y).term n = 1
    exact K.bagPair_one_left_term y n

  · intro a n
    refine Quotient.inductionOn a ?_
    intro x
    change (K.bagPair x .one).term n = 1
    exact K.bagPair_one_right_term x n

  · intro a b c n
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    change
      (K.bagPair (x * y) z).term n =
        (K.bagPair x z).term n *
        (K.bagPair y z).term n
    exact K.bagPair_mul_left_term x y z n

  · intro a b c n
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    change
      (K.bagPair x (y * z)).term n =
        (K.bagPair x y).term n *
        (K.bagPair x z).term n
    exact K.bagPair_mul_right_term x y z n

end PrimePairStreamSeed

namespace MultisetStreamCouplingSeed

/--
Forget the canonical output stream but retain its completed value.

This connects the prime-pair construction directly to the already-established
finite barcode coupling layer.
-/
def toBarcodeSeed
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C) :
    BarcodeCouplingSeed where

  couple := fun a b =>
    MulReal.ofStream (C.realize a b)

  one_left := by
    intro b
    change
      MulReal.ofStream (C.realize 1 b) =
        MulReal.ofStream (MulCauchyStream.constant 1)
    apply MulReal.ofStream_eq_of_asymptotic
    apply MulAsymptotic.of_pointwise
    intro n
    exact hC.one_left b n

  one_right := by
    intro a
    change
      MulReal.ofStream (C.realize a 1) =
        MulReal.ofStream (MulCauchyStream.constant 1)
    apply MulReal.ofStream_eq_of_asymptotic
    apply MulAsymptotic.of_pointwise
    intro n
    exact hC.one_right a n

  mul_left := by
    intro a b c
    change
      MulReal.ofStream (C.realize (a * b) c) =
        MulReal.ofStream (C.realize a c) *
          MulReal.ofStream (C.realize b c)
    change
      MulReal.ofStream (C.realize (a * b) c) =
        MulReal.ofStream
          (MulCauchyStream.mul
            (C.realize a c)
            (C.realize b c))
    apply MulReal.ofStream_eq_of_asymptotic
    apply MulAsymptotic.of_pointwise
    intro n
    exact hC.mul_left a b c n

  mul_right := by
    intro a b c
    change
      MulReal.ofStream (C.realize a (b * c)) =
        MulReal.ofStream (C.realize a b) *
          MulReal.ofStream (C.realize a c)
    change
      MulReal.ofStream (C.realize a (b * c)) =
        MulReal.ofStream
          (MulCauchyStream.mul
            (C.realize a b)
            (C.realize a c))
    apply MulReal.ofStream_eq_of_asymptotic
    apply MulAsymptotic.of_pointwise
    intro n
    exact hC.mul_right a b c n

end MultisetStreamCouplingSeed

namespace PrimePairStreamSeed

/--
Prime-pair streams plus the explicit unique-factorization descent theorem
produce the finite positive-barcode coupling seed used by `CouplingFinite`.
-/
def toBarcodeSeed
    (K : PrimePairStreamSeed)
    (hSame : K.RespectsSame) :
    BarcodeCouplingSeed :=
  let C := K.toMultiset hSame
  C.toBarcodeSeed (K.toMultiset_lawful hSame)

end PrimePairStreamSeed

end PrimeTensor
