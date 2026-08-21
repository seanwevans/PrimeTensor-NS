import PrimeTensor.Bridge.Real
import Mathlib.Data.Nat.Factors

/-!
# Reverse encoding of positive magnitudes into native prime barcodes

This is a bridge construction.  Natural-number factorization is used only to
turn an externally specified positive magnitude back into the native
`PrimeBag` / `PrimeMultiset` / `MulRat` representation.

The native representation itself is unchanged.
-/

namespace PrimeTensor
namespace Bridge
namespace Encode

/-- Rebuild an ordered native prime bag from a list of proof-carrying primes. -/
def bagOfPrimeList : List Prime → PrimeBag
  | [] => .one
  | p :: rest =>
      .factor p (bagOfPrimeList rest)

@[simp] theorem eval_bagOfPrimeList :
    ∀ ps : List Prime,
      PrimeBag.eval (bagOfPrimeList ps) =
        (ps.map Prime.value).prod
  | [] => rfl
  | p :: rest => by
      change
        p.value *
            PrimeBag.eval (bagOfPrimeList rest) =
          p.value *
            ((rest.map Prime.value).prod)
      rw [eval_bagOfPrimeList rest]

/--
Proof-carrying prime list extracted from the conventional natural
factorization.
-/
def primeList (n : ℕ) : List Prime :=
  n.primeFactorsList.attach.map
    (fun p =>
      ⟨p.val,
        Nat.prime_of_mem_primeFactorsList p.property⟩)

/-- Forgetting primality proofs recovers the canonical natural factor list. -/
theorem primeList_values
    (n : ℕ) :
    (primeList n).map Prime.value =
      n.primeFactorsList := by

  unfold primeList
  rw [List.map_map]

  change
    n.primeFactorsList.attach.map
        (fun p => p.val) =
      n.primeFactorsList

  simpa using
    (List.attach_map_val
      (l := n.primeFactorsList)
      (f := fun x : ℕ => x))

/-- Native ordered prime bag representing the positive natural magnitude `n`. -/
def bag (n : ℕ) : PrimeBag :=
  bagOfPrimeList (primeList n)

/--
For a nonzero natural magnitude, reverse encoding evaluates exactly to that
magnitude.
-/
theorem bag_eval
    {n : ℕ}
    (hn : n ≠ 0) :
    PrimeBag.eval (bag n) = n := by

  unfold bag
  rw [eval_bagOfPrimeList]
  rw [primeList_values]
  exact Nat.prod_primeFactorsList hn

/-- Native commutative prime multiset representing a positive natural. -/
def multiset (n : ℕ) : PrimeMultiset :=
  PrimeMultiset.ofBag (bag n)

/-- Reverse-encoded positive natural has the requested quotient magnitude. -/
theorem multiset_eval
    {n : ℕ}
    (hn : n ≠ 0) :
    PrimeMultiset.eval (multiset n) = n := by

  unfold multiset
  rw [PrimeMultiset.eval_ofBag]
  exact bag_eval hn

/--
Encode an externally supplied ratio of two positive natural magnitudes as a
native finite multiplicative rational.
-/
def ratio
    (upper lower : ℕ)
    (_hu : upper ≠ 0)
    (_hl : lower ≠ 0) :
    PrimeTensor.MulRat :=
  PrimeTensor.MulRat.ofRatio
    {
      upper := multiset upper
      lower := multiset lower
    }

/--
The conventional rational projection of the reverse-encoded ratio is exactly
the original natural ratio.
-/
theorem ratio_toRat
    (upper lower : ℕ)
    (hu : upper ≠ 0)
    (hl : lower ≠ 0) :
    PrimeTensor.Bridge.MulRat.toRat
        (ratio upper lower hu hl) =
      (upper : ℚ) / (lower : ℚ) := by

  change
    PrimeTensor.Bridge.PrimeRatio.toRat
        {
          upper := multiset upper
          lower := multiset lower
        } =
      (upper : ℚ) / (lower : ℚ)

  unfold PrimeTensor.Bridge.PrimeRatio.toRat

  rw [
    multiset_eval hu,
    multiset_eval hl
  ]

/--
The conventional real projection of the reverse-encoded ratio is the same
natural ratio cast into the reals.
-/
theorem ratio_toReal
    (upper lower : ℕ)
    (hu : upper ≠ 0)
    (hl : lower ≠ 0) :
    PrimeTensor.Bridge.MulRat.toReal
        (ratio upper lower hu hl) =
      (upper : ℝ) / (lower : ℝ) := by

  unfold PrimeTensor.Bridge.MulRat.toReal
  rw [ratio_toRat upper lower hu hl]
  simp only [Rat.cast_div, Rat.cast_natCast]

end Encode
end Bridge
end PrimeTensor
