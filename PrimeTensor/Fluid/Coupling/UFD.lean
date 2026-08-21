import PrimeTensor.Fluid.Coupling.Descent

/-!
# Unique-factorization descent for prime-pair coupling

`CouplingDescent` isolated `PrimePairStreamSeed.RespectsSame` as the remaining
number-theoretic obligation.  This file proves it.

The proof deliberately uses only the conventional natural-number
factorization theorem at this representation boundary:

* every `PrimeBag` becomes a list of proof-carrying prime atoms;
* mapping those atoms to natural values gives a list of primes whose product is
  exactly `PrimeBag.eval`;
* `Nat.primeFactorsList_unique` says two such lists with equal product are
  permutations of the same canonical prime-factor list;
* injectivity of `Prime.value` lifts that permutation back to the
  proof-carrying `Prime` lists;
* the recursively generated coupling term is invariant under independent
  permutations of either prime list because `MulRat` multiplication is
  commutative and associative.

Thus every `PrimePairStreamSeed` automatically respects `PrimeBag.Same`.  No
symmetry condition on the kernel `K p q` is required.
-/

namespace PrimeTensor

namespace Prime

/-- The natural value uniquely determines a proof-carrying prime atom. -/
theorem value_injective :
    Function.Injective Prime.value := by
  intro p q h
  cases p with
  | mk pv hp =>
      cases q with
      | mk qv hq =>
          cases h
          rfl

end Prime

namespace PrimeBag

/-- Ordered prime atoms underlying a factor chain. -/
def toPrimeList : PrimeBag → List Prime
  | .one => []
  | .factor p rest => p :: toPrimeList rest

@[simp] theorem toPrimeList_one :
    toPrimeList .one = [] := rfl

@[simp] theorem toPrimeList_factor
    (p : Prime) (rest : PrimeBag) :
    toPrimeList (.factor p rest) =
      p :: toPrimeList rest := rfl

/--
The product of the natural values in the prime list is exactly the bag
evaluation.
-/
theorem values_prod :
    ∀ b : PrimeBag,
      ((toPrimeList b).map Prime.value).prod =
        b.eval
  | .one => rfl
  | .factor p rest => by
      change
        p.value *
            ((toPrimeList rest).map Prime.value).prod =
          p.value * rest.eval
      rw [values_prod rest]

/-- Every value occurring in the list extracted from a prime bag is prime. -/
theorem value_mem_prime
    (b : PrimeBag) :
    ∀ q : ℕ,
      q ∈ (toPrimeList b).map Prime.value →
      Nat.Prime q := by
  intro q hq
  rcases List.mem_map.mp hq with
    ⟨p, hp, rfl⟩
  exact p.prime

/--
Equal evaluated prime bags contain exactly the same proof-carrying prime atoms,
up to permutation.
-/
theorem toPrimeList_perm_of_same
    {a b : PrimeBag}
    (h : Same a b) :
    (toPrimeList a).Perm (toPrimeList b) := by

  have ha :
      ((toPrimeList a).map Prime.value).Perm
        a.eval.primeFactorsList :=
    Nat.primeFactorsList_unique
      (values_prod a)
      (value_mem_prime a)

  have hb :
      ((toPrimeList b).map Prime.value).Perm
        b.eval.primeFactorsList :=
    Nat.primeFactorsList_unique
      (values_prod b)
      (value_mem_prime b)

  have hb' :
      ((toPrimeList b).map Prime.value).Perm
        a.eval.primeFactorsList := by
    rw [h]
    exact hb

  have hvalues :
      ((toPrimeList a).map Prime.value).Perm
        ((toPrimeList b).map Prime.value) :=
    ha.trans hb'.symm

  exact
    (List.map_perm_map_iff
      Prime.value_injective).mp hvalues

end PrimeBag

namespace PrimePairStreamSeed

/--
At one fixed approximation stage, couple one prime against a list of primes.
-/
def primeListTerm
    (K : PrimePairStreamSeed)
    (p : Prime)
    (n : Depth) :
    List Prime → MulRat
  | [] => 1
  | q :: rest =>
      (K.realize p q).term n *
        primeListTerm K p n rest

/--
At one fixed approximation stage, couple every prime in the left list against
every prime in the right list.
-/
def pairListTerm
    (K : PrimePairStreamSeed)
    (n : Depth) :
    List Prime → List Prime → MulRat
  | [], _ => 1
  | p :: rest, b =>
      primeListTerm K p n b *
        pairListTerm K n rest b

/-- The list presentation agrees exactly with `primeAgainstBag`. -/
theorem primeAgainstBag_term_eq_list
    (K : PrimePairStreamSeed)
    (p : Prime)
    (n : Depth) :
    ∀ b : PrimeBag,
      (K.primeAgainstBag p b).term n =
        K.primeListTerm p n (PrimeBag.toPrimeList b)
  | .one => rfl
  | .factor q rest => by
      change
        (K.realize p q).term n *
            (K.primeAgainstBag p rest).term n =
          (K.realize p q).term n *
            K.primeListTerm p n
              (PrimeBag.toPrimeList rest)
      rw [primeAgainstBag_term_eq_list K p n rest]

/-- The list presentation agrees exactly with `bagPair`. -/
theorem bagPair_term_eq_list
    (K : PrimePairStreamSeed)
    (n : Depth) :
    ∀ a b : PrimeBag,
      (K.bagPair a b).term n =
        K.pairListTerm n
          (PrimeBag.toPrimeList a)
          (PrimeBag.toPrimeList b)
  | .one, b => rfl
  | .factor p rest, b => by
      change
        (K.primeAgainstBag p b).term n *
            (K.bagPair rest b).term n =
          K.primeListTerm p n
              (PrimeBag.toPrimeList b) *
            K.pairListTerm n
              (PrimeBag.toPrimeList rest)
              (PrimeBag.toPrimeList b)
      rw [
        primeAgainstBag_term_eq_list K p n b,
        bagPair_term_eq_list K n rest b
      ]

/--
Coupling one fixed prime against a prime list is invariant under permutation of
that list.
-/
theorem primeListTerm_perm
    (K : PrimePairStreamSeed)
    (p : Prime)
    (n : Depth)
    {a b : List Prime}
    (h : a.Perm b) :
    K.primeListTerm p n a =
      K.primeListTerm p n b := by

  induction h with

  | nil =>
      rfl

  | cons q h ih =>
      change
        (K.realize p q).term n *
            K.primeListTerm p n _ =
          (K.realize p q).term n *
            K.primeListTerm p n _
      rw [ih]

  | swap q r rest =>
      change
        (K.realize p r).term n *
            ((K.realize p q).term n *
              K.primeListTerm p n rest) =
          (K.realize p q).term n *
            ((K.realize p r).term n *
              K.primeListTerm p n rest)
      calc
        (K.realize p r).term n *
            ((K.realize p q).term n *
              K.primeListTerm p n rest)
            =
          ((K.realize p r).term n *
              (K.realize p q).term n) *
            K.primeListTerm p n rest :=
              (MulRat.mul_assoc _ _ _).symm
        _ =
          ((K.realize p q).term n *
              (K.realize p r).term n) *
            K.primeListTerm p n rest := by
              rw [MulRat.mul_comm
                ((K.realize p r).term n)
                ((K.realize p q).term n)]
        _ =
          (K.realize p q).term n *
            ((K.realize p r).term n *
              K.primeListTerm p n rest) :=
              MulRat.mul_assoc _ _ _

  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/--
The pair-list term is invariant under permutation of the left prime list.
-/
theorem pairListTerm_perm_left
    (K : PrimePairStreamSeed)
    (n : Depth)
    {a a' : List Prime}
    (b : List Prime)
    (h : a.Perm a') :
    K.pairListTerm n a b =
      K.pairListTerm n a' b := by

  induction h with

  | nil =>
      rfl

  | cons p h ih =>
      change
        K.primeListTerm p n b *
            K.pairListTerm n _ b =
          K.primeListTerm p n b *
            K.pairListTerm n _ b
      rw [ih]

  | swap p q rest =>
      change
        K.primeListTerm q n b *
            (K.primeListTerm p n b *
              K.pairListTerm n rest b) =
          K.primeListTerm p n b *
            (K.primeListTerm q n b *
              K.pairListTerm n rest b)
      calc
        K.primeListTerm q n b *
            (K.primeListTerm p n b *
              K.pairListTerm n rest b)
            =
          (K.primeListTerm q n b *
              K.primeListTerm p n b) *
            K.pairListTerm n rest b :=
              (MulRat.mul_assoc _ _ _).symm
        _ =
          (K.primeListTerm p n b *
              K.primeListTerm q n b) *
            K.pairListTerm n rest b := by
              rw [MulRat.mul_comm
                (K.primeListTerm q n b)
                (K.primeListTerm p n b)]
        _ =
          K.primeListTerm p n b *
            (K.primeListTerm q n b *
              K.pairListTerm n rest b) :=
              MulRat.mul_assoc _ _ _

  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/--
The pair-list term is invariant under permutation of the right prime list.
-/
theorem pairListTerm_perm_right
    (K : PrimePairStreamSeed)
    (n : Depth)
    (a : List Prime)
    {b b' : List Prime}
    (h : b.Perm b') :
    K.pairListTerm n a b =
      K.pairListTerm n a b' := by

  induction a with

  | nil =>
      rfl

  | cons p rest ih =>
      change
        K.primeListTerm p n b *
            K.pairListTerm n rest b =
          K.primeListTerm p n b' *
            K.pairListTerm n rest b'
      rw [
        K.primeListTerm_perm p n h,
        ih
      ]

/--
Unique factorization proves the previously explicit `RespectsSame` obligation
for every prime-pair stream seed.
-/
theorem respectsSame
    (K : PrimePairStreamSeed) :
    K.RespectsSame where

  term_eq := by
    intro a a' b b' ha hb n

    rw [
      K.bagPair_term_eq_list n a b,
      K.bagPair_term_eq_list n a' b'
    ]

    have hleft :
        (PrimeBag.toPrimeList a).Perm
          (PrimeBag.toPrimeList a') :=
      PrimeBag.toPrimeList_perm_of_same ha

    have hright :
        (PrimeBag.toPrimeList b).Perm
          (PrimeBag.toPrimeList b') :=
      PrimeBag.toPrimeList_perm_of_same hb

    calc
      K.pairListTerm n
          (PrimeBag.toPrimeList a)
          (PrimeBag.toPrimeList b)
          =
        K.pairListTerm n
          (PrimeBag.toPrimeList a')
          (PrimeBag.toPrimeList b) :=
            K.pairListTerm_perm_left
              n
              (PrimeBag.toPrimeList b)
              hleft
      _ =
        K.pairListTerm n
          (PrimeBag.toPrimeList a')
          (PrimeBag.toPrimeList b') :=
            K.pairListTerm_perm_right
              n
              (PrimeBag.toPrimeList a')
              hright

/--
Canonical multiset descent: no external UFD hypothesis is needed anymore.
-/
def toMultisetCanonical
    (K : PrimePairStreamSeed) :
    MultisetStreamCouplingSeed :=
  K.toMultiset K.respectsSame

/-- The canonical multiset descent is termwise bilinear. -/
theorem toMultisetCanonical_lawful
    (K : PrimePairStreamSeed) :
    IsMultisetStreamCouplingSeed
      K.toMultisetCanonical :=
  K.toMultiset_lawful K.respectsSame

/--
Canonical finite positive-barcode coupling generated by prime-pair streams.
-/
def toBarcodeSeedCanonical
    (K : PrimePairStreamSeed) :
    BarcodeCouplingSeed :=
  K.toBarcodeSeed K.respectsSame

/--
Canonical finite rational coupling generated by prime-pair streams.
-/
def toFiniteCanonical
    (K : PrimePairStreamSeed) :
    FiniteMulCoupling :=
  K.toBarcodeSeedCanonical.toFinite

/-- The canonical finite rational coupling is bilinear. -/
theorem toFiniteCanonical_lawful
    (K : PrimePairStreamSeed) :
    IsFiniteMulCoupling K.toFiniteCanonical :=
  BarcodeCouplingSeed.toFinite_lawful
    K.toBarcodeSeedCanonical

end PrimePairStreamSeed

end PrimeTensor
