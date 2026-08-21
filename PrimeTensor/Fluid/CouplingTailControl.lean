import PrimeTensor.Fluid.CouplingControl

/-!
# Tail-local scale control for coupling completion

`CouplingUniformScaleControl` is sufficient for completion, but stronger than
needed for nonlinear couplings such as multiplication in logarithmic
coordinates.  Global uniform continuity is not the natural condition there.

This file weakens the analytic hypothesis in the native language.

For each pair of input Cauchy streams, control is required only on the tail
actually visited by those streams:

* canonical output streams must be uniformly Cauchy only for finite input
  values occurring on that tail;
* finite-input continuity must be uniform only in neighborhoods centered on
  that same tail.

The condition still proves exactly the two obligations needed by
`IsCouplingCompletionStable`:

1. diagonal outputs are Cauchy;
2. asymptotically equivalent input representatives yield asymptotically
   equivalent diagonal outputs.

No additive metric, logarithm, norm, or external boundedness predicate is
introduced.
-/

namespace PrimeTensor

/--
Tail-local intrinsic scale control for a canonical stream-valued finite
coupling.

Unlike `CouplingUniformScaleControl`, the witnesses may depend on the two
specific input Cauchy streams.
-/
structure CouplingTailScaleControl
    (C : StreamFiniteMulCoupling) : Prop where

  /--
  Along the tail of two fixed input Cauchy streams, the internal approximation
  stage of the canonical finite-output stream is uniformly Cauchy.

  One common anchor is used for the input-tail center `m` and the two output
  stages `r,s`; separate anchors would be equivalent after taking a finite
  `Depth.join`.
  -/
  output_cauchy :
    ∀ (a b : MulCauchyStream) (level : Depth),
      ∃ anchor : Depth,
        ∀ m r s : Depth,
          Depth.AtOrAfter anchor m →
          Depth.AtOrAfter anchor r →
          Depth.AtOrAfter anchor s →
          MulRat.ScaleWithin level
            ((C.realize (a.term m) (b.term m)).term r)
            ((C.realize (a.term m) (b.term m)).term s)

  /--
  Along the tail of two fixed input streams, sufficiently close finite inputs
  near a tail center produce sufficiently close canonical outputs at every
  sufficiently late common output stage.
  -/
  input_control :
    ∀ (a b : MulCauchyStream) (target : Depth),
      ∃ sourceA sourceB anchor : Depth,
        ∀ m n : Depth,
          Depth.AtOrAfter anchor m →
          Depth.AtOrAfter anchor n →
          ∀ a' b' : MulRat,
            MulRat.ScaleWithin sourceA (a.term m) a' →
            MulRat.ScaleWithin sourceB (b.term m) b' →
            MulRat.ScaleWithin target
              ((C.realize (a.term m) (b.term m)).term n)
              ((C.realize a' b').term n)

namespace CouplingTailScaleControl

variable
  {C : StreamFiniteMulCoupling}

/--
Tail-local scale control implies that every diagonalized output is
intrinsically Cauchy.
-/
theorem diagonalCauchy
    (hC : CouplingTailScaleControl C) :
    C.DiagonalCauchy := by

  intro a b level

  obtain ⟨outputAnchor, hOutput⟩ :=
    hC.output_cauchy a b (.succ level)

  obtain ⟨sourceA, sourceB, inputAnchor, hInput⟩ :=
    hC.input_control a b (.succ level)

  obtain ⟨aAnchor, ha⟩ :=
    a.cauchy sourceA

  obtain ⟨bAnchor, hb⟩ :=
    b.cauchy sourceB

  let abAnchor :=
    Depth.join aAnchor bAnchor

  let anchor :=
    Depth.join3 outputAnchor inputAnchor abAnchor

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  have hmOutput :
      Depth.AtOrAfter outputAnchor m :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hm

  have hnOutput :
      Depth.AtOrAfter outputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hn

  have hmInput :
      Depth.AtOrAfter inputAnchor m :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hm

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hn

  have hmAB :
      Depth.AtOrAfter abAnchor m :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hm

  have hnAB :
      Depth.AtOrAfter abAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        outputAnchor inputAnchor abAnchor)
      hn

  have hmA :
      Depth.AtOrAfter aAnchor m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hmAB

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hnAB

  have hmB :
      Depth.AtOrAfter bAnchor m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hmAB

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hnAB

  have hInternalLeg :
      MulRat.ScaleWithin (.succ level)
        ((C.realize (a.term m) (b.term m)).term m)
        ((C.realize (a.term m) (b.term m)).term n) :=
    hOutput
      m m n
      hmOutput hmOutput hnOutput

  have hInputLeg :
      MulRat.ScaleWithin (.succ level)
        ((C.realize (a.term m) (b.term m)).term n)
        ((C.realize (a.term n) (b.term n)).term n) :=
    hInput
      m n
      hmInput hnInput
      (a.term n) (b.term n)
      (ha m n hmA hnA)
      (hb m n hmB hnB)

  exact
    MulRat.scaleWithin_comp
      hInternalLeg hInputLeg

/--
Tail-local input control is sufficient for diagonalization to respect
asymptotically equivalent input representatives.

The local neighborhood is centered on the tail of the unprimed
representatives; asymptoticity eventually puts the primed representatives
inside that neighborhood.
-/
theorem diagonalAsymptotic
    (hC : CouplingTailScaleControl C)
    {a a' b b' : MulCauchyStream}
    (ha : MulAsymptotic a a')
    (hb : MulAsymptotic b b') :
    MulAsymptotic
      (C.diagonal hC.diagonalCauchy a b)
      (C.diagonal hC.diagonalCauchy a' b') := by

  intro level

  obtain ⟨sourceA, sourceB, controlAnchor, hInput⟩ :=
    hC.input_control a b level

  obtain ⟨aAnchor, haTail⟩ :=
    ha sourceA

  obtain ⟨bAnchor, hbTail⟩ :=
    hb sourceB

  let anchor :=
    Depth.join3 controlAnchor aAnchor bAnchor

  refine ⟨anchor, ?_⟩
  intro n hn

  have hnControl :
      Depth.AtOrAfter controlAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        controlAnchor aAnchor bAnchor)
      hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        controlAnchor aAnchor bAnchor)
      hn

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        controlAnchor aAnchor bAnchor)
      hn

  exact
    hInput
      n n
      hnControl hnControl
      (a'.term n) (b'.term n)
      (haTail n hnA)
      (hbTail n hnB)

/--
Tail-local scale control implies the exact quotient-level completion stability
required by `StreamFiniteMulCoupling.complete`.
-/
theorem toCompletionStable
    (hC : CouplingTailScaleControl C) :
    IsCouplingCompletionStable C where

  diagonal_cauchy :=
    hC.diagonalCauchy

  diagonal_asymptotic := by
    intro a a' b b' ha hb
    exact
      hC.diagonalAsymptotic ha hb

end CouplingTailScaleControl

namespace CouplingUniformScaleControl

variable
  {C : StreamFiniteMulCoupling}

/--
The previous global uniform criterion is a special case of tail-local control.
Thus this file is a genuine weakening of the completion hypothesis rather than
a competing completion construction.
-/
theorem toTailScaleControl
    (hC : CouplingUniformScaleControl C) :
    CouplingTailScaleControl C where

  output_cauchy := by
    intro a b level

    obtain ⟨anchor, hOutput⟩ :=
      hC.output_cauchy level

    refine ⟨anchor, ?_⟩
    intro m r s hm hr hs

    exact
      hOutput
        (a.term m) (b.term m)
        r s hr hs

  input_control := by
    intro a b target

    obtain ⟨sourceA, sourceB, anchor, hInput⟩ :=
      hC.input_control target

    refine ⟨sourceA, sourceB, anchor, ?_⟩
    intro m n hm hn a' b' ha hb

    exact
      hInput
        (a.term m) a'
        (b.term m) b'
        n
        hn
        ha hb

end CouplingUniformScaleControl

namespace StreamFiniteMulCoupling

/--
A termwise-bilinear realizer with tail-local intrinsic scale control yields a
lawful coupling on the entire completed carrier.
-/
theorem complete_lawful_of_tailScaleControl
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hScale : CouplingTailScaleControl C) :
    IsMulCoupling
      (C.complete hScale.toCompletionStable) := by

  exact
    C.complete_lawful
      hAlg
      hScale.toCompletionStable

/--
The tail-locally controlled completion agrees with an earlier finite coupling
on embedded finite barcodes whenever the stream realizer realizes it.
-/
theorem complete_agrees_finite_of_tailScaleControl
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F)
    (hScale : CouplingTailScaleControl C)
    (a b : MulRat) :
    (C.complete hScale.toCompletionStable).couple
        (MulReal.ofRat a)
        (MulReal.ofRat b) =
      F.couple a b := by

  exact
    C.complete_agrees_finite
      F hRealize hScale.toCompletionStable a b

end StreamFiniteMulCoupling

end PrimeTensor
