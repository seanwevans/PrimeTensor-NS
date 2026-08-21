import PrimeTensor.Fluid.CouplingFinite

/-!
# Completion of the intrinsic coupling

A finite coupling whose values already live in `MulReal` is not by itself enough
to define coupling on arbitrary completed inputs: quotienting has forgotten the
specific Cauchy stream that produced each output.

This file keeps that missing constructive data explicitly.

A `StreamFiniteMulCoupling` assigns each pair of finite barcodes a canonical
multiplicative Cauchy stream.  Completion then requires exactly two analytic
facts:

1. diagonalizing those canonical output streams along two input Cauchy streams
   is again Cauchy;
2. asymptotically equivalent input representatives produce asymptotically
   equivalent diagonal outputs.

Once those are supplied, the operation lifts through the quotient.  Exact
termwise bilinearity of the canonical realizers then proves the completed
operation satisfies `IsMulCoupling`.

No additive operation, additive identity, subtraction, ordinary logarithm, or
ordinary real coefficient is introduced.
-/

namespace PrimeTensor

/--
Canonical stream-level realization of finite coupling.

The output has not yet been quotiented, so it retains the approximation data
needed for a second completion argument.
-/
structure StreamFiniteMulCoupling where
  realize : MulRat → MulRat → MulCauchyStream

namespace StreamFiniteMulCoupling

/--
Diagonalize the canonical finite-output approximation along two input streams.
-/
def diagonalTerm
    (C : StreamFiniteMulCoupling)
    (a b : MulCauchyStream) :
    MulStream :=
  fun n =>
    (C.realize (a.term n) (b.term n)).term n

/--
The first completion obligation: every diagonal output is intrinsically Cauchy.
-/
def DiagonalCauchy
    (C : StreamFiniteMulCoupling) : Prop :=
  ∀ a b : MulCauchyStream,
    IsMulCauchy (C.diagonalTerm a b)

/--
Package a diagonal output as a Cauchy stream once the first completion
obligation is known.
-/
def diagonal
    (C : StreamFiniteMulCoupling)
    (hCauchy : C.DiagonalCauchy)
    (a b : MulCauchyStream) :
    MulCauchyStream where
  term := C.diagonalTerm a b
  cauchy := hCauchy a b

@[simp] theorem diagonal_term
    (C : StreamFiniteMulCoupling)
    (hCauchy : C.DiagonalCauchy)
    (a b : MulCauchyStream)
    (n : Depth) :
    (C.diagonal hCauchy a b).term n =
      (C.realize (a.term n) (b.term n)).term n := rfl

end StreamFiniteMulCoupling

/--
Exact algebraic laws for the canonical finite realizers.

The laws are termwise, not merely quotient equalities.  This is what lets
bilinearity survive diagonalization without any extra analytic argument.
-/
structure IsStreamFiniteMulCoupling
    (C : StreamFiniteMulCoupling) : Prop where

  one_left :
    ∀ (b : MulRat) (n : Depth),
      (C.realize 1 b).term n = 1

  one_right :
    ∀ (a : MulRat) (n : Depth),
      (C.realize a 1).term n = 1

  mul_left :
    ∀ (a b c : MulRat) (n : Depth),
      (C.realize (a * b) c).term n =
        (C.realize a c).term n *
        (C.realize b c).term n

  mul_right :
    ∀ (a b c : MulRat) (n : Depth),
      (C.realize a (b * c)).term n =
        (C.realize a b).term n *
        (C.realize a c).term n

/--
The genuinely analytic completion condition.

`diagonal_cauchy` says the diagonal construction exists as a completed point.
`diagonal_asymptotic` says that construction is independent of the chosen
Cauchy representatives of the two inputs.
-/
structure IsCouplingCompletionStable
    (C : StreamFiniteMulCoupling) : Prop where

  diagonal_cauchy :
    C.DiagonalCauchy

  diagonal_asymptotic :
    ∀ {a a' b b' : MulCauchyStream},
      MulAsymptotic a a' →
      MulAsymptotic b b' →
      MulAsymptotic
        (C.diagonal diagonal_cauchy a b)
        (C.diagonal diagonal_cauchy a' b')

namespace StreamFiniteMulCoupling

/--
Lift a completion-stable stream coupling to the completed multiplicative
carrier.
-/
def complete
    (C : StreamFiniteMulCoupling)
    (hC : IsCouplingCompletionStable C) :
    MulCoupling where
  couple := fun a b =>
    Quotient.liftOn₂ a b
      (fun x y =>
        MulReal.ofStream
          (C.diagonal hC.diagonal_cauchy x y))
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        change MulAsymptotic a₁ a₂ at ha
        change MulAsymptotic b₁ b₂ at hb
        apply MulReal.ofStream_eq_of_asymptotic
        exact hC.diagonal_asymptotic ha hb)

/--
On two embedded finite barcodes, completed coupling is exactly the completed
canonical finite-output stream.
-/
theorem complete_ofRat
    (C : StreamFiniteMulCoupling)
    (hC : IsCouplingCompletionStable C)
    (a b : MulRat) :
    (C.complete hC).couple
        (MulReal.ofRat a)
        (MulReal.ofRat b) =
      MulReal.ofStream (C.realize a b) := by

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          (MulCauchyStream.constant a)
          (MulCauchyStream.constant b)) =
      MulReal.ofStream (C.realize a b)

  apply MulReal.ofStream_eq_of_asymptotic
  apply MulAsymptotic.of_pointwise
  intro n
  rfl

/--
The completed coupling sends the pivot in the first slot to the pivot.
-/
theorem complete_one_left
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (b : MulReal) :
    (C.complete hC).couple 1 b = 1 := by

  refine Quotient.inductionOn b ?_
  intro y

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          (MulCauchyStream.constant 1) y) =
      MulReal.ofStream (MulCauchyStream.constant 1)

  apply MulReal.ofStream_eq_of_asymptotic
  apply MulAsymptotic.of_pointwise
  intro n
  exact hAlg.one_left (y.term n) n

/--
The completed coupling sends the pivot in the second slot to the pivot.
-/
theorem complete_one_right
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (a : MulReal) :
    (C.complete hC).couple a 1 = 1 := by

  refine Quotient.inductionOn a ?_
  intro x

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          x (MulCauchyStream.constant 1)) =
      MulReal.ofStream (MulCauchyStream.constant 1)

  apply MulReal.ofStream_eq_of_asymptotic
  apply MulAsymptotic.of_pointwise
  intro n
  exact hAlg.one_right (x.term n) n

/--
Diagonal coupling preserves multiplication in the first completed argument.
-/
theorem complete_mul_left
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (a b c : MulReal) :
    (C.complete hC).couple (a * b) c =
      (C.complete hC).couple a c *
      (C.complete hC).couple b c := by

  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          (MulCauchyStream.mul x y) z) =
      MulReal.ofStream
        (MulCauchyStream.mul
          (C.diagonal hC.diagonal_cauchy x z)
          (C.diagonal hC.diagonal_cauchy y z))

  apply MulReal.ofStream_eq_of_asymptotic
  apply MulAsymptotic.of_pointwise
  intro n
  exact hAlg.mul_left
    (x.term n) (y.term n) (z.term n) n

/--
Diagonal coupling preserves multiplication in the second completed argument.
-/
theorem complete_mul_right
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (a b c : MulReal) :
    (C.complete hC).couple a (b * c) =
      (C.complete hC).couple a b *
      (C.complete hC).couple a c := by

  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          x (MulCauchyStream.mul y z)) =
      MulReal.ofStream
        (MulCauchyStream.mul
          (C.diagonal hC.diagonal_cauchy x y)
          (C.diagonal hC.diagonal_cauchy x z))

  apply MulReal.ofStream_eq_of_asymptotic
  apply MulAsymptotic.of_pointwise
  intro n
  exact hAlg.mul_right
    (x.term n) (y.term n) (z.term n) n

/--
A completion-stable termwise-bilinear realizer produces a lawful intrinsic
coupling on all of `MulReal`.
-/
theorem complete_lawful
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C) :
    IsMulCoupling (C.complete hC) where

  couple_one_left :=
    C.complete_one_left hAlg hC

  couple_one_right :=
    C.complete_one_right hAlg hC

  couple_mul_left :=
    C.complete_mul_left hAlg hC

  couple_mul_right :=
    C.complete_mul_right hAlg hC

end StreamFiniteMulCoupling

/--
A canonical stream realizer may be tied back to the already-constructed
`FiniteMulCoupling` by requiring its quotient value to agree on every finite
input pair.
-/
def RealizesFiniteCoupling
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling) : Prop :=
  ∀ a b : MulRat,
    MulReal.ofStream (C.realize a b) =
      F.couple a b

namespace StreamFiniteMulCoupling

/--
The completed operation agrees with the earlier finite coupling on the dense
finite barcode embedding whenever the stream realizer realizes that finite
coupling.
-/
theorem complete_agrees_finite
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F)
    (hC : IsCouplingCompletionStable C)
    (a b : MulRat) :
    (C.complete hC).couple
        (MulReal.ofRat a)
        (MulReal.ofRat b) =
      F.couple a b := by
  rw [C.complete_ofRat hC a b]
  exact hRealize a b

end StreamFiniteMulCoupling

end PrimeTensor
