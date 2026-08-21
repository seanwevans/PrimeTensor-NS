import PrimeTensor.ScaleLaws

/-!
# Intrinsic multiplicative completion

The analytic notion of closeness is indexed by positive `Depth` and measured by
`MulRat.ScaleWithin`.  There is no arbitrary additive tolerance and no zeroth
sequence index.

This file proves that asymptotic equivalence is an equivalence relation and
forms the quotient carrier `MulReal`.
-/

namespace PrimeTensor

namespace Depth

/--
`AtOrAfter anchor n` means that `n` lies in the tail beginning at `anchor`.
-/
inductive AtOrAfter : Depth → Depth → Prop where
  | here (n : Depth) : AtOrAfter n n
  | later {anchor n : Depth} :
      AtOrAfter anchor n → AtOrAfter anchor (.succ n)

/-- Every positive index lies at or after the first index. -/
theorem one_atOrAfter : ∀ n : Depth, AtOrAfter .one n
  | .one => .here .one
  | .succ n => .later (one_atOrAfter n)

/-- Tail membership lifts through successor on both endpoints. -/
theorem succ_atOrAfter {a b : Depth} :
    AtOrAfter a b → AtOrAfter (.succ a) (.succ b) := by
  intro h
  induction h with
  | here =>
      exact .here _
  | later h ih =>
      exact .later ih

/-- Tail membership is transitive. -/
theorem atOrAfter_trans {a b c : Depth}
    (hab : AtOrAfter a b) (hbc : AtOrAfter b c) :
    AtOrAfter a c := by
  induction hbc with
  | here =>
      exact hab
  | later h ih =>
      exact .later ih

/--
Native common-tail anchor.  This is the positive-index analogue of taking the
later of two sequence stages.
-/
def join : Depth → Depth → Depth
  | .one, b => b
  | .succ a, .one => .succ a
  | .succ a, .succ b => .succ (join a b)

/-- The common-tail anchor lies at or after its left input. -/
theorem left_atOrAfter : ∀ a b : Depth, AtOrAfter a (join a b)
  | .one, b => one_atOrAfter b
  | .succ a, .one => .here (.succ a)
  | .succ a, .succ b => succ_atOrAfter (left_atOrAfter a b)

/-- The common-tail anchor lies at or after its right input. -/
theorem right_atOrAfter : ∀ a b : Depth, AtOrAfter b (join a b)
  | .one, b => .here b
  | .succ a, .one => one_atOrAfter (.succ a)
  | .succ a, .succ b => succ_atOrAfter (right_atOrAfter a b)

end Depth

/-- A multiplicative rational stream indexed from the first positive stage. -/
abbrev MulStream := Depth → MulRat

/--
A stream is multiplicatively Cauchy when every intrinsic scale eventually
contains every pair of terms in one tail.
-/
def IsMulCauchy (s : MulStream) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ m n : Depth,
        Depth.AtOrAfter anchor m →
        Depth.AtOrAfter anchor n →
        MulRat.ScaleWithin level (s m) (s n)

/-- A multiplicatively Cauchy prime-rational stream. -/
structure MulCauchyStream where
  term : MulStream
  cauchy : IsMulCauchy term

namespace MulCauchyStream

/-- Constant streams are multiplicatively Cauchy. -/
def constant (q : MulRat) : MulCauchyStream where
  term := fun _ => q
  cauchy := by
    intro level
    refine ⟨.one, ?_⟩
    intro m n hm hn
    exact MulRat.scaleWithin_refl level q

@[simp] theorem constant_term (q : MulRat) (n : Depth) :
    (constant q).term n = q := rfl

end MulCauchyStream

/--
Two Cauchy streams are asymptotic when corresponding terms eventually become
close at every intrinsic scale.
-/
def MulAsymptotic (a b : MulCauchyStream) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        MulRat.ScaleWithin level (a.term n) (b.term n)

namespace MulAsymptotic

@[refl] theorem refl (a : MulCauchyStream) : MulAsymptotic a a := by
  intro level
  refine ⟨.one, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_refl level (a.term n)

@[symm] theorem symm {a b : MulCauchyStream} :
    MulAsymptotic a b → MulAsymptotic b a := by
  intro hab level
  obtain ⟨anchor, htail⟩ := hab level
  refine ⟨anchor, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_symm (htail n hn)

/--
Asymptotic equivalence is transitive because one finer scale on each leg
composes into the requested scale.
-/
@[trans] theorem trans {a b c : MulCauchyStream}
    (hab : MulAsymptotic a b) (hbc : MulAsymptotic b c) :
    MulAsymptotic a c := by
  intro level
  obtain ⟨abAnchor, habTail⟩ := hab (.succ level)
  obtain ⟨bcAnchor, hbcTail⟩ := hbc (.succ level)
  let anchor := Depth.join abAnchor bcAnchor
  refine ⟨anchor, ?_⟩
  intro n hn
  have habN : Depth.AtOrAfter abAnchor n :=
    Depth.atOrAfter_trans (Depth.left_atOrAfter abAnchor bcAnchor) hn
  have hbcN : Depth.AtOrAfter bcAnchor n :=
    Depth.atOrAfter_trans (Depth.right_atOrAfter abAnchor bcAnchor) hn
  exact MulRat.scaleWithin_comp (habTail n habN) (hbcTail n hbcN)

/-- The explicit setoid used by the multiplicative completion. -/
def setoid : Setoid MulCauchyStream where
  r := MulAsymptotic
  iseqv := ⟨refl, @symm, @trans⟩

end MulAsymptotic

/--
The multiplicative completion carrier: intrinsic Cauchy streams modulo
intrinsic asymptotic equivalence.
-/
abbrev MulReal := Quotient MulAsymptotic.setoid

namespace MulReal

/-- Inject a Cauchy stream into the completion quotient. -/
def ofStream (s : MulCauchyStream) : MulReal :=
  Quotient.mk MulAsymptotic.setoid s

/-- Embed a finite positive rational prime barcode as a constant stream. -/
def ofRat (q : MulRat) : MulReal :=
  ofStream (MulCauchyStream.constant q)

/-- Multiplicative pivot in the completion. -/
def one : MulReal := ofRat 1

instance : One MulReal := ⟨one⟩

end MulReal

end PrimeTensor
