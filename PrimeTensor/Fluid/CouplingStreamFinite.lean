import PrimeTensor.Fluid.CouplingDescent

/-!
# Stream-preserving finite coupling

`CouplingDescent` constructs a canonical `MulCauchyStream` for each pair of
positive prime multisets.  The existing `toBarcodeSeed` then immediately
forgets that stream and retains only its quotient value in `MulReal`.

For completion we need the opposite choice: preserve the canonical stream while
extending both positive multiset inputs across oriented rational barcodes.

This file is the stream-level analogue of `CouplingFinite`.

It proves:

* oriented stream ratios respect `PrimeRatio.Same`;
* both multiplicative laws hold term by term after orientation;
* the construction descends to `MulRat × MulRat`;
* the descended realizer satisfies `IsStreamFiniteMulCoupling`.

No conventional real operation, logarithm, additive identity, or signed prime
exponent is introduced.
-/

namespace PrimeTensor

namespace MulRat

/--
Cross-product equality implies equality of native oriented ratios.

This is the finite-barcode analogue of `MulReal.ratio_eq_of_cross`.
-/
theorem ratio_eq_of_cross
    {a b c d : MulRat}
    (h : a * d = c * b) :
    ratio a b = ratio c d := by

  calc
    ratio a b
        =
      ratio a b * ratio d d := by
        rw [ratio_self, mul_one]

    _ =
      ratio (a * d) (b * d) :=
        (ratio_mul_pair a b d d).symm

    _ =
      ratio (c * b) (b * d) := by
        rw [h]

    _ =
      ratio c b * ratio b d :=
        ratio_mul_pair c b b d

    _ =
      ratio c d :=
        (ratio_comp c b d).symm

end MulRat

namespace MulCauchyStream

/-- Pointwise oriented ratio of two intrinsic Cauchy streams. -/
def ratio
    (a b : MulCauchyStream) :
    MulCauchyStream :=
  mul a (inv b)

@[simp] theorem ratio_term
    (a b : MulCauchyStream)
    (n : Depth) :
    (ratio a b).term n =
      MulRat.ratio (a.term n) (b.term n) := by
  rfl

end MulCauchyStream

namespace MultisetStreamCouplingSeed

/--
Orient the first positive-multiset input while preserving the canonical output
stream.
-/
def orientedLeftStream
    (C : MultisetStreamCouplingSeed)
    (a : PrimeRatio)
    (b : PrimeMultiset) :
    MulCauchyStream :=
  MulCauchyStream.ratio
    (C.realize a.upper b)
    (C.realize a.lower b)

/--
The stream-oriented first slot respects rational representative equivalence.
-/
theorem orientedLeftStream_same
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    {a a' : PrimeRatio}
    (h : PrimeRatio.Same a a')
    (b : PrimeMultiset) :
    orientedLeftStream C a b =
      orientedLeftStream C a' b := by

  have hcross :
      a.upper * a'.lower =
        a'.upper * a.lower := by

    apply PrimeMultiset.eq_of_eval_eq

    change
      a.upper.eval * a'.lower.eval =
        a'.upper.eval * a.lower.eval at h

    simpa only [PrimeMultiset.eval_mul] using h

  apply MulCauchyStream.eq_of_term_eq
  intro n

  change
    MulRat.ratio
        ((C.realize a.upper b).term n)
        ((C.realize a.lower b).term n) =
      MulRat.ratio
        ((C.realize a'.upper b).term n)
        ((C.realize a'.lower b).term n)

  apply MulRat.ratio_eq_of_cross

  calc
    (C.realize a.upper b).term n *
        (C.realize a'.lower b).term n
        =
      (C.realize (a.upper * a'.lower) b).term n :=
        (hC.mul_left
          a.upper a'.lower b n).symm

    _ =
      (C.realize (a'.upper * a.lower) b).term n := by
        rw [hcross]

    _ =
      (C.realize a'.upper b).term n *
        (C.realize a.lower b).term n :=
          hC.mul_left
            a'.upper a.lower b n

@[simp] theorem orientedLeftStream_one_first_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (b : PrimeMultiset)
    (n : Depth) :
    (orientedLeftStream C 1 b).term n = 1 := by

  change
    MulRat.ratio
        ((C.realize 1 b).term n)
        ((C.realize 1 b).term n) =
      1

  exact MulRat.ratio_self _

@[simp] theorem orientedLeftStream_one_second_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a : PrimeRatio)
    (n : Depth) :
    (orientedLeftStream C a 1).term n = 1 := by

  change
    MulRat.ratio
        ((C.realize a.upper 1).term n)
        ((C.realize a.lower 1).term n) =
      1

  rw [
    hC.one_right a.upper n,
    hC.one_right a.lower n,
    MulRat.ratio_self
  ]

/--
After first-slot orientation, multiplication in the remaining positive slot is
still exact term by term.
-/
theorem orientedLeftStream_mul_second_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a : PrimeRatio)
    (b c : PrimeMultiset)
    (n : Depth) :
    (orientedLeftStream C a (b * c)).term n =
      (orientedLeftStream C a b).term n *
        (orientedLeftStream C a c).term n := by

  change
    MulRat.ratio
        ((C.realize a.upper (b * c)).term n)
        ((C.realize a.lower (b * c)).term n) =
      MulRat.ratio
          ((C.realize a.upper b).term n)
          ((C.realize a.lower b).term n) *
        MulRat.ratio
          ((C.realize a.upper c).term n)
          ((C.realize a.lower c).term n)

  rw [
    hC.mul_right a.upper b c n,
    hC.mul_right a.lower b c n
  ]

  exact
    MulRat.ratio_mul_pair
      ((C.realize a.upper b).term n)
      ((C.realize a.lower b).term n)
      ((C.realize a.upper c).term n)
      ((C.realize a.lower c).term n)

/--
First-slot orientation itself preserves multiplication of oriented
representatives, term by term.
-/
theorem orientedLeftStream_mul_first_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a a' : PrimeRatio)
    (b : PrimeMultiset)
    (n : Depth) :
    (orientedLeftStream C (a * a') b).term n =
      (orientedLeftStream C a b).term n *
        (orientedLeftStream C a' b).term n := by

  change
    MulRat.ratio
        ((C.realize (a.upper * a'.upper) b).term n)
        ((C.realize (a.lower * a'.lower) b).term n) =
      MulRat.ratio
          ((C.realize a.upper b).term n)
          ((C.realize a.lower b).term n) *
        MulRat.ratio
          ((C.realize a'.upper b).term n)
          ((C.realize a'.lower b).term n)

  rw [
    hC.mul_left a.upper a'.upper b n,
    hC.mul_left a.lower a'.lower b n
  ]

  exact
    MulRat.ratio_mul_pair
      ((C.realize a.upper b).term n)
      ((C.realize a.lower b).term n)
      ((C.realize a'.upper b).term n)
      ((C.realize a'.lower b).term n)

/--
Orient the second rational representative as well, retaining the full canonical
Cauchy stream.
-/
def coupleRatioStream
    (C : MultisetStreamCouplingSeed)
    (a b : PrimeRatio) :
    MulCauchyStream :=
  MulCauchyStream.ratio
    (orientedLeftStream C a b.upper)
    (orientedLeftStream C a b.lower)

@[simp] theorem coupleRatioStream_one_left_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (b : PrimeRatio)
    (n : Depth) :
    (coupleRatioStream C 1 b).term n = 1 := by

  change
    MulRat.ratio
        ((orientedLeftStream C 1 b.upper).term n)
        ((orientedLeftStream C 1 b.lower).term n) =
      1

  rw [
    orientedLeftStream_one_first_term C hC b.upper n,
    orientedLeftStream_one_first_term C hC b.lower n,
    MulRat.ratio_self
  ]

@[simp] theorem coupleRatioStream_one_right_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a : PrimeRatio)
    (n : Depth) :
    (coupleRatioStream C a 1).term n = 1 := by

  change
    MulRat.ratio
        ((orientedLeftStream C a 1).term n)
        ((orientedLeftStream C a 1).term n) =
      1

  exact MulRat.ratio_self _

/-- Second oriented input is multiplicative term by term. -/
theorem coupleRatioStream_mul_right_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a b c : PrimeRatio)
    (n : Depth) :
    (coupleRatioStream C a (b * c)).term n =
      (coupleRatioStream C a b).term n *
        (coupleRatioStream C a c).term n := by

  change
    MulRat.ratio
        ((orientedLeftStream C a (b.upper * c.upper)).term n)
        ((orientedLeftStream C a (b.lower * c.lower)).term n) =
      MulRat.ratio
          ((orientedLeftStream C a b.upper).term n)
          ((orientedLeftStream C a b.lower).term n) *
        MulRat.ratio
          ((orientedLeftStream C a c.upper).term n)
          ((orientedLeftStream C a c.lower).term n)

  rw [
    orientedLeftStream_mul_second_term
      C hC a b.upper c.upper n,
    orientedLeftStream_mul_second_term
      C hC a b.lower c.lower n
  ]

  exact
    MulRat.ratio_mul_pair
      ((orientedLeftStream C a b.upper).term n)
      ((orientedLeftStream C a b.lower).term n)
      ((orientedLeftStream C a c.upper).term n)
      ((orientedLeftStream C a c.lower).term n)

/-- First oriented input is multiplicative term by term. -/
theorem coupleRatioStream_mul_left_term
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a a' b : PrimeRatio)
    (n : Depth) :
    (coupleRatioStream C (a * a') b).term n =
      (coupleRatioStream C a b).term n *
        (coupleRatioStream C a' b).term n := by

  change
    MulRat.ratio
        ((orientedLeftStream C (a * a') b.upper).term n)
        ((orientedLeftStream C (a * a') b.lower).term n) =
      MulRat.ratio
          ((orientedLeftStream C a b.upper).term n)
          ((orientedLeftStream C a b.lower).term n) *
        MulRat.ratio
          ((orientedLeftStream C a' b.upper).term n)
          ((orientedLeftStream C a' b.lower).term n)

  rw [
    orientedLeftStream_mul_first_term
      C hC a a' b.upper n,
    orientedLeftStream_mul_first_term
      C hC a a' b.lower n
  ]

  exact
    MulRat.ratio_mul_pair
      ((orientedLeftStream C a b.upper).term n)
      ((orientedLeftStream C a b.lower).term n)
      ((orientedLeftStream C a' b.upper).term n)
      ((orientedLeftStream C a' b.lower).term n)

/-- Representative equivalence in the first rational input preserves streams. -/
theorem coupleRatioStream_same_left
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    {a a' b : PrimeRatio}
    (h : PrimeRatio.Same a a') :
    coupleRatioStream C a b =
      coupleRatioStream C a' b := by

  apply MulCauchyStream.eq_of_term_eq
  intro n

  change
    MulRat.ratio
        ((orientedLeftStream C a b.upper).term n)
        ((orientedLeftStream C a b.lower).term n) =
      MulRat.ratio
        ((orientedLeftStream C a' b.upper).term n)
        ((orientedLeftStream C a' b.lower).term n)

  have hu :=
    congrArg
      (fun s : MulCauchyStream => s.term n)
      (orientedLeftStream_same C hC h b.upper)

  have hl :=
    congrArg
      (fun s : MulCauchyStream => s.term n)
      (orientedLeftStream_same C hC h b.lower)

  rw [hu, hl]

/-- Representative equivalence in the second rational input preserves streams. -/
theorem coupleRatioStream_same_right
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    {a b b' : PrimeRatio}
    (h : PrimeRatio.Same b b') :
    coupleRatioStream C a b =
      coupleRatioStream C a b' := by

  have hcross :
      b.upper * b'.lower =
        b'.upper * b.lower := by

    apply PrimeMultiset.eq_of_eval_eq

    change
      b.upper.eval * b'.lower.eval =
        b'.upper.eval * b.lower.eval at h

    simpa only [PrimeMultiset.eval_mul] using h

  apply MulCauchyStream.eq_of_term_eq
  intro n

  change
    MulRat.ratio
        ((orientedLeftStream C a b.upper).term n)
        ((orientedLeftStream C a b.lower).term n) =
      MulRat.ratio
        ((orientedLeftStream C a b'.upper).term n)
        ((orientedLeftStream C a b'.lower).term n)

  apply MulRat.ratio_eq_of_cross

  calc
    (orientedLeftStream C a b.upper).term n *
        (orientedLeftStream C a b'.lower).term n
        =
      (orientedLeftStream C a (b.upper * b'.lower)).term n :=
        (orientedLeftStream_mul_second_term
          C hC a b.upper b'.lower n).symm

    _ =
      (orientedLeftStream C a (b'.upper * b.lower)).term n := by
        rw [hcross]

    _ =
      (orientedLeftStream C a b'.upper).term n *
        (orientedLeftStream C a b.lower).term n :=
          orientedLeftStream_mul_second_term
            C hC a b'.upper b.lower n

/--
Descend the stream-preserving oriented construction through both `MulRat`
quotients.
-/
def toStreamFinite
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C) :
    StreamFiniteMulCoupling where

  realize := fun a b =>
    Quotient.liftOn₂ a b
      (fun x y =>
        coupleRatioStream C x y)
      (by
        intro a₁ b₁ a₂ b₂ ha hb

        change PrimeRatio.Same a₁ a₂ at ha
        change PrimeRatio.Same b₁ b₂ at hb

        calc
          coupleRatioStream C a₁ b₁
              =
            coupleRatioStream C a₂ b₁ :=
              coupleRatioStream_same_left
                C hC ha

          _ =
            coupleRatioStream C a₂ b₂ :=
              coupleRatioStream_same_right
                C hC hb)

/--
The stream-preserving finite extension satisfies exact termwise bilinearity.
-/
theorem toStreamFinite_lawful
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C) :
    IsStreamFiniteMulCoupling
      (C.toStreamFinite hC) := by

  constructor

  · intro b n
    refine Quotient.inductionOn b ?_
    intro y
    exact
      coupleRatioStream_one_left_term
        C hC y n

  · intro a n
    refine Quotient.inductionOn a ?_
    intro x
    exact
      coupleRatioStream_one_right_term
        C hC x n

  · intro a b c n
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    exact
      coupleRatioStream_mul_left_term
        C hC x y z n

  · intro a b c n
    refine Quotient.inductionOn a ?_
    intro x
    refine Quotient.inductionOn b ?_
    intro y
    refine Quotient.inductionOn c ?_
    intro z
    exact
      coupleRatioStream_mul_right_term
        C hC x y z n

end MultisetStreamCouplingSeed

end PrimeTensor
