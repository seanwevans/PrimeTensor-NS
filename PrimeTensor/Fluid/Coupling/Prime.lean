import PrimeTensor.Fluid.Coupling.Control

/-!
# Prime-pair realization of finite coupling

The nonlinear coupling data can be pushed down one more level.

Instead of assigning a coupling value to every pair of finite barcodes, it is
enough algebraically to assign a canonical Cauchy stream to every pair of prime
atoms.  Coupling of composite factor chains is then the nonempty-ended recursive
product over all prime pairs.

This file works first on `PrimeBag`, before quotienting by represented natural
magnitude.  It proves the exact termwise bilinearity needed later.  The next
step is the unique-factorization theorem showing that these term functions are
invariant under `PrimeBag.Same`, allowing them to descend to
`PrimeMultiset`/`MulRat`.

No additive operation or signed prime exponent is introduced.
-/

namespace PrimeTensor

/--
Canonical completed approximation attached to one pair of prime atoms.
-/
structure PrimePairStreamSeed where
  realize : Prime → Prime → MulCauchyStream

namespace PrimePairStreamSeed

/--
Couple one prime against every factor in a positive prime bag.
-/
def primeAgainstBag
    (K : PrimePairStreamSeed)
    (p : Prime) :
    PrimeBag → MulCauchyStream
  | .one =>
      MulCauchyStream.constant 1
  | .factor q rest =>
      MulCauchyStream.mul
        (K.realize p q)
        (primeAgainstBag K p rest)

/--
Couple every prime in the left bag against every prime in the right bag.
-/
def bagPair
    (K : PrimePairStreamSeed) :
    PrimeBag → PrimeBag → MulCauchyStream
  | .one, _ =>
      MulCauchyStream.constant 1
  | .factor p rest, b =>
      MulCauchyStream.mul
        (primeAgainstBag K p b)
        (bagPair K rest b)

@[simp] theorem primeAgainstBag_one_term
    (K : PrimePairStreamSeed)
    (p : Prime)
    (n : Depth) :
    (K.primeAgainstBag p .one).term n = 1 := rfl

@[simp] theorem primeAgainstBag_factor_term
    (K : PrimePairStreamSeed)
    (p q : Prime)
    (rest : PrimeBag)
    (n : Depth) :
    (K.primeAgainstBag p (.factor q rest)).term n =
      (K.realize p q).term n *
      (K.primeAgainstBag p rest).term n := rfl

@[simp] theorem bagPair_one_left_term
    (K : PrimePairStreamSeed)
    (b : PrimeBag)
    (n : Depth) :
    (K.bagPair .one b).term n = 1 := rfl

@[simp] theorem bagPair_factor_left_term
    (K : PrimePairStreamSeed)
    (p : Prime)
    (rest b : PrimeBag)
    (n : Depth) :
    (K.bagPair (.factor p rest) b).term n =
      (K.primeAgainstBag p b).term n *
      (K.bagPair rest b).term n := rfl

/-- Local four-factor shuffle in the finite barcode carrier. -/
private theorem mul_four_shuffle
    (a b c d : MulRat) :
    (a * b) * (c * d) =
      (a * c) * (b * d) := by
  calc
    (a * b) * (c * d)
        = a * (b * (c * d)) :=
          MulRat.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := by
          rw [← MulRat.mul_assoc b c d]
    _ = a * ((c * b) * d) := by
          rw [MulRat.mul_comm b c]
    _ = a * (c * (b * d)) := by
          rw [MulRat.mul_assoc c b d]
    _ = (a * c) * (b * d) :=
          (MulRat.mul_assoc a c (b * d)).symm

/--
Coupling one prime against bag concatenation is termwise multiplicative.
-/
theorem primeAgainstBag_mul_term
    (K : PrimePairStreamSeed)
    (p : Prime) :
    ∀ (a b : PrimeBag) (n : Depth),
      (K.primeAgainstBag p (a * b)).term n =
        (K.primeAgainstBag p a).term n *
        (K.primeAgainstBag p b).term n
  | .one, b, n => by
      change
        (K.primeAgainstBag p b).term n =
          1 * (K.primeAgainstBag p b).term n
      exact
        (MulRat.one_mul
          ((K.primeAgainstBag p b).term n)).symm

  | .factor q rest, b, n => by
      change
        (K.realize p q).term n *
            (K.primeAgainstBag p (rest * b)).term n =
          ((K.realize p q).term n *
              (K.primeAgainstBag p rest).term n) *
            (K.primeAgainstBag p b).term n
      rw [primeAgainstBag_mul_term K p rest b n]
      exact
        (MulRat.mul_assoc
          ((K.realize p q).term n)
          ((K.primeAgainstBag p rest).term n)
          ((K.primeAgainstBag p b).term n)).symm

/--
Bag-pair coupling is termwise multiplicative in the first factor chain.
-/
theorem bagPair_mul_left_term
    (K : PrimePairStreamSeed) :
    ∀ (a b c : PrimeBag) (n : Depth),
      (K.bagPair (a * b) c).term n =
        (K.bagPair a c).term n *
        (K.bagPair b c).term n
  | .one, b, c, n => by
      change
        (K.bagPair b c).term n =
          1 * (K.bagPair b c).term n
      exact
        (MulRat.one_mul
          ((K.bagPair b c).term n)).symm

  | .factor p rest, b, c, n => by
      change
        (K.primeAgainstBag p c).term n *
            (K.bagPair (rest * b) c).term n =
          ((K.primeAgainstBag p c).term n *
              (K.bagPair rest c).term n) *
            (K.bagPair b c).term n
      rw [bagPair_mul_left_term K rest b c n]
      exact
        (MulRat.mul_assoc
          ((K.primeAgainstBag p c).term n)
          ((K.bagPair rest c).term n)
          ((K.bagPair b c).term n)).symm

/--
Bag-pair coupling is termwise multiplicative in the second factor chain.
-/
theorem bagPair_mul_right_term
    (K : PrimePairStreamSeed) :
    ∀ (a b c : PrimeBag) (n : Depth),
      (K.bagPair a (b * c)).term n =
        (K.bagPair a b).term n *
        (K.bagPair a c).term n
  | .one, b, c, n => by
      change (1 : MulRat) = 1 * 1
      exact (MulRat.one_mul 1).symm

  | .factor p rest, b, c, n => by
      change
        (K.primeAgainstBag p (b * c)).term n *
            (K.bagPair rest (b * c)).term n =
          ((K.primeAgainstBag p b).term n *
              (K.bagPair rest b).term n) *
            ((K.primeAgainstBag p c).term n *
              (K.bagPair rest c).term n)

      rw [primeAgainstBag_mul_term K p b c n]
      rw [bagPair_mul_right_term K rest b c n]

      exact mul_four_shuffle
        ((K.primeAgainstBag p b).term n)
        ((K.primeAgainstBag p c).term n)
        ((K.bagPair rest b).term n)
        ((K.bagPair rest c).term n)

/--
Coupling against the pivot bag is termwise the pivot.
-/
theorem bagPair_one_right_term
    (K : PrimePairStreamSeed) :
    ∀ (a : PrimeBag) (n : Depth),
      (K.bagPair a .one).term n = 1
  | .one, n => rfl

  | .factor p rest, n => by
      change
        1 * (K.bagPair rest .one).term n = 1
      rw [bagPair_one_right_term K rest n]
      exact MulRat.one_mul 1

/--
The prime-pair recursion is therefore exactly bilinear on ordered factor
chains, term by term.
-/
theorem bagPair_termwise_bilinear
    (K : PrimePairStreamSeed) :
    (∀ (b : PrimeBag) (n : Depth),
      (K.bagPair .one b).term n = 1) ∧
    (∀ (a : PrimeBag) (n : Depth),
      (K.bagPair a .one).term n = 1) ∧
    (∀ (a b c : PrimeBag) (n : Depth),
      (K.bagPair (a * b) c).term n =
        (K.bagPair a c).term n *
        (K.bagPair b c).term n) ∧
    (∀ (a b c : PrimeBag) (n : Depth),
      (K.bagPair a (b * c)).term n =
        (K.bagPair a b).term n *
        (K.bagPair a c).term n) := by
  exact ⟨
    bagPair_one_left_term K,
    bagPair_one_right_term K,
    bagPair_mul_left_term K,
    bagPair_mul_right_term K
  ⟩

/--
Pointwise symmetry of the prime-pair seed.
-/
def Symmetric
    (K : PrimePairStreamSeed) : Prop :=
  ∀ (p q : Prime) (n : Depth),
    (K.realize p q).term n =
      (K.realize q p).term n

end PrimePairStreamSeed

end PrimeTensor
