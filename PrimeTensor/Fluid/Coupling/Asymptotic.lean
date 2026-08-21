import PrimeTensor.Fluid.Coupling.Normalize

/-!
# Asymptotic algebra laws for stream-level finite couplings

Rate normalization repairs convergence scheduling but may choose different
reindexing functions for different finite input pairs.  Consequently it need
not preserve the old exact *termwise* bilinearity equations.

The quotient value is what matters for completion.  This file replaces exact
termwise algebra laws by asymptotic laws between the corresponding canonical
streams.

The central generic theorem is simple but important:

If a `StreamFiniteMulCoupling C` realizes a lawful quotient-level
`FiniteMulCoupling F`, then the stream equations for the unit and both
multiplicative slots hold up to `MulAsymptotic`.

The proof uses only the defining quotient:

    equal `MulReal` values
      => related stream representatives

via `Quotient.exact`.

No conventional real bridge appears here.
-/

namespace PrimeTensor

namespace MulCauchyStream

/-- Quotienting pointwise stream multiplication is multiplication in `MulReal`. -/
theorem ofStream_mul
    (a b : MulCauchyStream) :
    MulReal.ofStream (mul a b) =
      MulReal.ofStream a * MulReal.ofStream b := by
  rfl

/-- The constant pivot stream represents the pivot of `MulReal`. -/
@[simp] theorem ofStream_constant_one :
    MulReal.ofStream (constant 1) = (1 : MulReal) := by
  rfl

end MulCauchyStream

/--
Algebra laws for a stream-level finite coupling, weakened from exact termwise
equality to intrinsic asymptotic equivalence.

This is the appropriate law notion for rate-normalized representatives.
-/
structure IsAsymptoticStreamFiniteMulCoupling
    (C : StreamFiniteMulCoupling) : Prop where

  one_left :
    ∀ b : MulRat,
      MulAsymptotic
        (C.realize 1 b)
        (MulCauchyStream.constant 1)

  one_right :
    ∀ a : MulRat,
      MulAsymptotic
        (C.realize a 1)
        (MulCauchyStream.constant 1)

  mul_left :
    ∀ a b c : MulRat,
      MulAsymptotic
        (C.realize (a * b) c)
        (
          MulCauchyStream.mul
            (C.realize a c)
            (C.realize b c)
        )

  mul_right :
    ∀ a b c : MulRat,
      MulAsymptotic
        (C.realize a (b * c))
        (
          MulCauchyStream.mul
            (C.realize a b)
            (C.realize a c)
        )

namespace StreamFiniteMulCoupling

/--
Any stream realizer of a lawful finite quotient coupling automatically
satisfies the corresponding stream algebra laws up to asymptotic equivalence.
-/
theorem asymptotic_lawful_of_realizesFinite
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F)
    (hF : IsFiniteMulCoupling F) :
    IsAsymptoticStreamFiniteMulCoupling C := by

  constructor

  · intro b

    have hq :
        MulReal.ofStream (C.realize 1 b) =
          MulReal.ofStream
            (MulCauchyStream.constant 1) := by
      calc
        MulReal.ofStream (C.realize 1 b)
            =
          F.couple 1 b :=
            hRealize 1 b

        _ = 1 :=
          hF.couple_one_left b

        _ =
          MulReal.ofStream
            (MulCauchyStream.constant 1) := by
              symm
              exact MulCauchyStream.ofStream_constant_one

    exact
      Quotient.exact
        (s := MulAsymptotic.setoid)
        hq

  · intro a

    have hq :
        MulReal.ofStream (C.realize a 1) =
          MulReal.ofStream
            (MulCauchyStream.constant 1) := by
      calc
        MulReal.ofStream (C.realize a 1)
            =
          F.couple a 1 :=
            hRealize a 1

        _ = 1 :=
          hF.couple_one_right a

        _ =
          MulReal.ofStream
            (MulCauchyStream.constant 1) := by
              symm
              exact MulCauchyStream.ofStream_constant_one

    exact
      Quotient.exact
        (s := MulAsymptotic.setoid)
        hq

  · intro a b c

    have hq :
        MulReal.ofStream (C.realize (a * b) c) =
          MulReal.ofStream
            (
              MulCauchyStream.mul
                (C.realize a c)
                (C.realize b c)
            ) := by
      calc
        MulReal.ofStream (C.realize (a * b) c)
            =
          F.couple (a * b) c :=
            hRealize (a * b) c

        _ =
          F.couple a c * F.couple b c :=
            hF.couple_mul_left a b c

        _ =
          MulReal.ofStream (C.realize a c) *
            MulReal.ofStream (C.realize b c) := by
              rw [
                hRealize a c,
                hRealize b c
              ]

        _ =
          MulReal.ofStream
            (
              MulCauchyStream.mul
                (C.realize a c)
                (C.realize b c)
            ) := by
              symm
              exact
                MulCauchyStream.ofStream_mul
                  (C.realize a c)
                  (C.realize b c)

    exact
      Quotient.exact
        (s := MulAsymptotic.setoid)
        hq

  · intro a b c

    have hq :
        MulReal.ofStream (C.realize a (b * c)) =
          MulReal.ofStream
            (
              MulCauchyStream.mul
                (C.realize a b)
                (C.realize a c)
            ) := by
      calc
        MulReal.ofStream (C.realize a (b * c))
            =
          F.couple a (b * c) :=
            hRealize a (b * c)

        _ =
          F.couple a b * F.couple a c :=
            hF.couple_mul_right a b c

        _ =
          MulReal.ofStream (C.realize a b) *
            MulReal.ofStream (C.realize a c) := by
              rw [
                hRealize a b,
                hRealize a c
              ]

        _ =
          MulReal.ofStream
            (
              MulCauchyStream.mul
                (C.realize a b)
                (C.realize a c)
            ) := by
              symm
              exact
                MulCauchyStream.ofStream_mul
                  (C.realize a b)
                  (C.realize a c)

    exact
      Quotient.exact
        (s := MulAsymptotic.setoid)
        hq

/--
Rate normalization therefore preserves finite algebra automatically at the
correct asymptotic level.
-/
theorem rateNormalized_asymptotic_lawful_of_realizesFinite
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F)
    (hF : IsFiniteMulCoupling F) :
    IsAsymptoticStreamFiniteMulCoupling
      C.rateNormalized := by

  exact
    asymptotic_lawful_of_realizesFinite
      C.rateNormalized
      F
      (C.rateNormalized_realizesFinite F hRealize)
      hF

end StreamFiniteMulCoupling

end PrimeTensor
