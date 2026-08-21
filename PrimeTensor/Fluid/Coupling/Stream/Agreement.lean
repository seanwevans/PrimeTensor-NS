import PrimeTensor.Fluid.Coupling.Stream.Finite

/-!
# Agreement of stream-preserving and quotient-level finite coupling

`CouplingDescent` originally forgets each canonical output stream immediately,
retaining only its class in `MulReal`, and then performs oriented-rational
extension there.

`CouplingStreamFinite` performs the same oriented-rational extension before
quotienting, preserving the canonical `MulCauchyStream`.

This file proves that these two routes agree exactly after quotienting.  Thus
the stream-preserving construction is a refinement of the already-established
finite coupling, not a parallel definition.
-/

namespace PrimeTensor

namespace MulCauchyStream

/-- Quotienting a pointwise stream ratio is the ratio of the quotient values. -/
theorem ofStream_ratio
    (a b : MulCauchyStream) :
    MulReal.ofStream (ratio a b) =
      MulReal.ratio
        (MulReal.ofStream a)
        (MulReal.ofStream b) := by
  rfl

end MulCauchyStream

namespace MultisetStreamCouplingSeed

/--
The stream-preserving first-slot orientation agrees after quotienting with the
older `BarcodeCouplingSeed.orientedLeft` construction.
-/
theorem ofStream_orientedLeftStream
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a : PrimeRatio)
    (b : PrimeMultiset) :
    MulReal.ofStream
        (orientedLeftStream C a b) =
      BarcodeCouplingSeed.orientedLeft
        (C.toBarcodeSeed hC)
        a b := by

  unfold orientedLeftStream
  rw [MulCauchyStream.ofStream_ratio]

  rfl

/--
The fully oriented stream construction agrees after quotienting with the older
`BarcodeCouplingSeed.coupleRatio` construction.
-/
theorem ofStream_coupleRatioStream
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C)
    (a b : PrimeRatio) :
    MulReal.ofStream
        (coupleRatioStream C a b) =
      BarcodeCouplingSeed.coupleRatio
        (C.toBarcodeSeed hC)
        a b := by

  unfold coupleRatioStream
  rw [MulCauchyStream.ofStream_ratio]

  change
    MulReal.ratio
        (MulReal.ofStream
          (orientedLeftStream C a b.upper))
        (MulReal.ofStream
          (orientedLeftStream C a b.lower)) =
      MulReal.ratio
        (BarcodeCouplingSeed.orientedLeft
          (C.toBarcodeSeed hC) a b.upper)
        (BarcodeCouplingSeed.orientedLeft
          (C.toBarcodeSeed hC) a b.lower)

  rw [
    ofStream_orientedLeftStream C hC a b.upper,
    ofStream_orientedLeftStream C hC a b.lower
  ]

/--
Quotienting the stream-preserving finite extension recovers exactly the finite
coupling obtained by quotienting first and orienting second.
-/
theorem toStreamFinite_realizes_toFinite
    (C : MultisetStreamCouplingSeed)
    (hC : IsMultisetStreamCouplingSeed C) :
    RealizesFiniteCoupling
      (C.toStreamFinite hC)
      ((C.toBarcodeSeed hC).toFinite) := by

  intro a b

  refine Quotient.inductionOn a ?_
  intro x

  refine Quotient.inductionOn b ?_
  intro y

  change
    MulReal.ofStream
        (coupleRatioStream C x y) =
      BarcodeCouplingSeed.coupleRatio
        (C.toBarcodeSeed hC)
        x y

  exact
    ofStream_coupleRatioStream
      C hC x y

end MultisetStreamCouplingSeed

end PrimeTensor
