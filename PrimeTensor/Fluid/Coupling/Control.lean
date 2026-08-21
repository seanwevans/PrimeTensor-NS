import PrimeTensor.Fluid.Coupling.Completion

/-!
# Quantitative scale control for coupling completion

`IsCouplingCompletionStable` is the exact quotient-level condition needed to
extend a stream-valued finite coupling to `MulReal`.  This file gives a stronger
but quantitative criterion from which that condition follows.

Two uniform estimates are required:

1. `output_cauchy`:
   the canonical output stream is uniformly Cauchy in its internal stage,
   independently of the finite input pair;

2. `input_control`:
   at a sufficiently late common output stage, sufficiently fine input
   closeness in each slot yields any requested output closeness.

The diagonal-Cauchy proof then has two legs:

    realize(aₘ,bₘ)[m]
      ~ realize(aₘ,bₘ)[n]
      ~ realize(aₙ,bₙ)[n].

Each leg is requested one intrinsic scale finer; `scaleWithin_comp` consumes
that one level and returns the desired scale.

No additive modulus, epsilon, zeroth index, subtraction, or ordinary metric is
introduced.
-/

namespace PrimeTensor

namespace Depth

/-- Common positive tail anchor for three stages. -/
def join3 (a b c : Depth) : Depth :=
  join a (join b c)

/-- `join3` lies at or after its first input. -/
theorem first_atOrAfter_join3
    (a b c : Depth) :
    AtOrAfter a (join3 a b c) := by
  unfold join3
  exact left_atOrAfter a (join b c)

/-- `join3` lies at or after its second input. -/
theorem second_atOrAfter_join3
    (a b c : Depth) :
    AtOrAfter b (join3 a b c) := by
  unfold join3
  exact atOrAfter_trans
    (left_atOrAfter b c)
    (right_atOrAfter a (join b c))

/-- `join3` lies at or after its third input. -/
theorem third_atOrAfter_join3
    (a b c : Depth) :
    AtOrAfter c (join3 a b c) := by
  unfold join3
  exact atOrAfter_trans
    (right_atOrAfter b c)
    (right_atOrAfter a (join b c))

end Depth

/--
Uniform intrinsic scale control for a canonical stream-valued finite coupling.
-/
structure CouplingUniformScaleControl
    (C : StreamFiniteMulCoupling) : Prop where

  /--
  Every canonical finite-output stream has one tail anchor that works uniformly
  for every finite input pair at the requested intrinsic scale.
  -/
  output_cauchy :
    ∀ level : Depth,
      ∃ anchor : Depth,
        ∀ a b : MulRat,
          ∀ m n : Depth,
            Depth.AtOrAfter anchor m →
            Depth.AtOrAfter anchor n →
            MulRat.ScaleWithin level
              ((C.realize a b).term m)
              ((C.realize a b).term n)

  /--
  Uniform two-input continuity at sufficiently late canonical output stages.
  -/
  input_control :
    ∀ target : Depth,
      ∃ sourceA sourceB outputAnchor : Depth,
        ∀ a a' b b' : MulRat,
          ∀ n : Depth,
            Depth.AtOrAfter outputAnchor n →
            MulRat.ScaleWithin sourceA a a' →
            MulRat.ScaleWithin sourceB b b' →
            MulRat.ScaleWithin target
              ((C.realize a b).term n)
              ((C.realize a' b').term n)

namespace CouplingUniformScaleControl

variable
  {C : StreamFiniteMulCoupling}

/--
Uniform scale control implies that every diagonalized output is intrinsically
Cauchy.
-/
theorem diagonalCauchy
    (hC : CouplingUniformScaleControl C) :
    C.DiagonalCauchy := by

  intro a b level

  obtain ⟨internalAnchor, hInternal⟩ :=
    hC.output_cauchy (.succ level)

  obtain ⟨sourceA, sourceB, inputAnchor, hInput⟩ :=
    hC.input_control (.succ level)

  obtain ⟨aAnchor, ha⟩ :=
    a.cauchy sourceA

  obtain ⟨bAnchor, hb⟩ :=
    b.cauchy sourceB

  let inputTail :=
    Depth.join3 inputAnchor aAnchor bAnchor

  let anchor :=
    Depth.join internalAnchor inputTail

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  have hmInternal :
      Depth.AtOrAfter internalAnchor m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter internalAnchor inputTail)
      hm

  have hnInternal :
      Depth.AtOrAfter internalAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter internalAnchor inputTail)
      hn

  have hmInputTail :
      Depth.AtOrAfter inputTail m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter internalAnchor inputTail)
      hm

  have hnInputTail :
      Depth.AtOrAfter inputTail n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter internalAnchor inputTail)
      hn

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hnInputTail

  have hmA :
      Depth.AtOrAfter aAnchor m :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hmInputTail

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hnInputTail

  have hmB :
      Depth.AtOrAfter bAnchor m :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hmInputTail

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hnInputTail

  have hInternalLeg :
      MulRat.ScaleWithin (.succ level)
        ((C.realize (a.term m) (b.term m)).term m)
        ((C.realize (a.term m) (b.term m)).term n) :=
    hInternal
      (a.term m) (b.term m)
      m n
      hmInternal hnInternal

  have hInputLeg :
      MulRat.ScaleWithin (.succ level)
        ((C.realize (a.term m) (b.term m)).term n)
        ((C.realize (a.term n) (b.term n)).term n) :=
    hInput
      (a.term m) (a.term n)
      (b.term m) (b.term n)
      n
      hnInput
      (ha m n hmA hnA)
      (hb m n hmB hnB)

  exact MulRat.scaleWithin_comp
    hInternalLeg hInputLeg

/--
Uniform input scale control makes diagonalization respect asymptotically
equivalent input representatives.
-/
theorem diagonalAsymptotic
    (hC : CouplingUniformScaleControl C)
    {a a' b b' : MulCauchyStream}
    (ha : MulAsymptotic a a')
    (hb : MulAsymptotic b b') :
    MulAsymptotic
      (C.diagonal hC.diagonalCauchy a b)
      (C.diagonal hC.diagonalCauchy a' b') := by

  intro level

  obtain ⟨sourceA, sourceB, inputAnchor, hInput⟩ :=
    hC.input_control level

  obtain ⟨aAnchor, haTail⟩ :=
    ha sourceA

  obtain ⟨bAnchor, hbTail⟩ :=
    hb sourceB

  let anchor :=
    Depth.join3 inputAnchor aAnchor bAnchor

  refine ⟨anchor, ?_⟩
  intro n hn

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hn

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3 inputAnchor aAnchor bAnchor)
      hn

  exact hInput
    (a.term n) (a'.term n)
    (b.term n) (b'.term n)
    n
    hnInput
    (haTail n hnA)
    (hbTail n hnB)

/--
Quantitative uniform control implies the exact completion-stability structure
needed by quotient lifting.
-/
def toCompletionStable
    (hC : CouplingUniformScaleControl C) :
    IsCouplingCompletionStable C where

  diagonal_cauchy :=
    hC.diagonalCauchy

  diagonal_asymptotic := by
    intro a a' b b' ha hb
    exact hC.diagonalAsymptotic ha hb

end CouplingUniformScaleControl

namespace StreamFiniteMulCoupling

/--
A termwise-bilinear realizer with uniform intrinsic scale control yields a
lawful coupling on the entire completed carrier.
-/
theorem complete_lawful_of_uniformScaleControl
    (C : StreamFiniteMulCoupling)
    (hAlg : IsStreamFiniteMulCoupling C)
    (hScale : CouplingUniformScaleControl C) :
    IsMulCoupling
      (C.complete hScale.toCompletionStable) := by
  exact C.complete_lawful
    hAlg
    hScale.toCompletionStable

/--
The uniformly-controlled completion also agrees with an earlier finite coupling
on embedded finite barcodes whenever the stream realizer realizes it.
-/
theorem complete_agrees_finite_of_uniformScaleControl
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F)
    (hScale : CouplingUniformScaleControl C)
    (a b : MulRat) :
    (C.complete hScale.toCompletionStable).couple
        (MulReal.ofRat a)
        (MulReal.ofRat b) =
      F.couple a b := by
  exact C.complete_agrees_finite
    F hRealize hScale.toCompletionStable a b

end StreamFiniteMulCoupling

end PrimeTensor
