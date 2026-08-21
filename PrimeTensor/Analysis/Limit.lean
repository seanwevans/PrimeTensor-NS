import PrimeTensor.Structure

/-!
# Intrinsic convergence on `MulReal`

A completed point is a class of multiplicative Cauchy streams.  We define
finite-scale nearness directly in terms of representatives and then define
convergence of positive-indexed `MulReal` sequences by eventual nearness at
every intrinsic scale.

The central theorem is that the embedded terms of every Cauchy stream converge
to the completed point represented by that stream.
-/

namespace PrimeTensor

namespace MulReal

/--
Two completed magnitudes are near at `level` when they admit representatives
whose tails are `ScaleWithin level`.

The existential choice of representatives is part of the quotient semantics;
no ordinary metric, subtraction, or additive epsilon is introduced.
-/
def ScaleNear (level : Depth) (x y : MulReal) : Prop :=
  ∃ a b : MulCauchyStream,
    ofStream a = x ∧
    ofStream b = y ∧
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        MulRat.ScaleWithin level (a.term n) (b.term n)

/-- Every completed point is near itself at every intrinsic scale. -/
theorem scaleNear_refl (level : Depth) (x : MulReal) :
    ScaleNear level x x := by
  refine Quotient.inductionOn x ?_
  intro a
  refine ⟨a, a, rfl, rfl, .one, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_refl level (a.term n)

/-- Finite-scale nearness is symmetric. -/
theorem scaleNear_symm {level : Depth} {x y : MulReal} :
    ScaleNear level x y → ScaleNear level y x := by
  intro h
  obtain ⟨a, b, hax, hby, anchor, htail⟩ := h
  refine ⟨b, a, hby, hax, anchor, ?_⟩
  intro n hn
  exact MulRat.scaleWithin_symm (htail n hn)

/-- A positive-indexed sequence of completed multiplicative magnitudes. -/
abbrev Seq := Depth → MulReal

/--
Intrinsic convergence: at every scale depth, the sequence eventually remains
near the target at that scale.
-/
def ConvergesTo (s : Seq) (x : MulReal) : Prop :=
  ∀ level : Depth,
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        ScaleNear level (s n) x

/-- Constant completed sequences converge to their constant value. -/
theorem converges_constant (x : MulReal) :
    ConvergesTo (fun _ => x) x := by
  intro level
  refine ⟨.one, ?_⟩
  intro n hn
  exact scaleNear_refl level x

/-- Asymptotic stream representatives determine the same completed point. -/
theorem ofStream_eq_of_asymptotic {a b : MulCauchyStream}
    (h : MulAsymptotic a b) :
    ofStream a = ofStream b := by
  exact Quotient.sound h

/--
The canonical convergence theorem for the completion.

If `a` is a multiplicative Cauchy stream, then its finite barcode terms,
embedded into `MulReal`, converge to the quotient point represented by `a`.
-/
theorem terms_converge (a : MulCauchyStream) :
    ConvergesTo (fun n => ofRat (a.term n)) (ofStream a) := by
  intro level
  obtain ⟨anchor, hcauchy⟩ := a.cauchy level
  refine ⟨anchor, ?_⟩
  intro n hn
  refine ⟨MulCauchyStream.constant (a.term n), a, rfl, rfl, anchor, ?_⟩
  intro k hk
  exact hcauchy n k hn hk

/--
Asymptotic representatives converge to the same completed point.
-/
theorem terms_converge_of_asymptotic {a b : MulCauchyStream}
    (h : MulAsymptotic a b) :
    ConvergesTo (fun n => ofRat (a.term n)) (ofStream b) := by
  have hab : ofStream a = ofStream b :=
    ofStream_eq_of_asymptotic h
  rw [← hab]
  exact terms_converge a

end MulReal

end PrimeTensor
