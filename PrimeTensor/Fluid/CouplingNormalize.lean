import PrimeTensor.Fluid.CouplingTailControl

/-!
# Cauchy-stream rate normalization

The same-depth diagonal used by `StreamFiniteMulCoupling` implicitly assumes
that the external input index is already late enough for the internal canonical
output stream.  That need not be true when finite input complexity grows much
faster than the external depth.

This file removes that accidental coupling of rates.

For every `MulCauchyStream s` and every intrinsic scale level, choose one
Cauchy anchor.  The cumulative normalization stage joins all anchors seen up to
the current positive depth.  Reindexing `s` along those cumulative stages gives
an asymptotically equivalent stream with a universal modulus:

    at scale `level`, every pair of normalized terms indexed at-or-after
    `level` is already `ScaleWithin level`.

Thus arbitrary convergence rates are converted into a canonical positive-depth
schedule without changing the represented `MulReal`.

No conventional metric, logarithm, additive identity, or zero index is used.
-/

namespace PrimeTensor

namespace MulCauchyStream

/-- One chosen native Cauchy anchor for one requested intrinsic scale. -/
noncomputable def scaleAnchor
    (s : MulCauchyStream)
    (level : Depth) :
    Depth :=
  Classical.choose (s.cauchy level)

/-- Specification of the chosen Cauchy anchor. -/
theorem scaleAnchor_spec
    (s : MulCauchyStream)
    (level : Depth) :
    ∀ m n : Depth,
      Depth.AtOrAfter (scaleAnchor s level) m →
      Depth.AtOrAfter (scaleAnchor s level) n →
      MulRat.ScaleWithin level
        (s.term m)
        (s.term n) :=
  Classical.choose_spec (s.cauchy level)

/--
Cumulative internal stage.

At each positive depth we retain every earlier chosen scale anchor and join in
the newly requested one.
-/
noncomputable def normalizationStage
    (s : MulCauchyStream) :
    Depth → Depth
  | .one =>
      scaleAnchor s .one
  | .succ d =>
      Depth.join
        (normalizationStage s d)
        (scaleAnchor s (.succ d))

/-- The cumulative stage at a level lies at or after that level's own anchor. -/
theorem scaleAnchor_atOrAfter_normalizationStage
    (s : MulCauchyStream) :
    ∀ level : Depth,
      Depth.AtOrAfter
        (scaleAnchor s level)
        (normalizationStage s level)
  | .one => by
      exact Depth.AtOrAfter.here _
  | .succ d => by
      change
        Depth.AtOrAfter
          (scaleAnchor s (.succ d))
          (Depth.join
            (normalizationStage s d)
            (scaleAnchor s (.succ d)))
      exact
        Depth.right_atOrAfter
          (normalizationStage s d)
          (scaleAnchor s (.succ d))

/--
If `n` is at or after `level`, the cumulative stage at `n` is already beyond
the chosen anchor for `level`.
-/
theorem scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
    (s : MulCauchyStream)
    {level n : Depth}
    (h : Depth.AtOrAfter level n) :
    Depth.AtOrAfter
      (scaleAnchor s level)
      (normalizationStage s n) := by

  induction h with

  | here =>
      exact
        scaleAnchor_atOrAfter_normalizationStage
          s level

  | later h ih =>
      exact
        Depth.atOrAfter_trans
          ih
          (Depth.left_atOrAfter
            (normalizationStage s _)
            (scaleAnchor s (.succ _)))

/--
Rate-normalized stream.

The value is unchanged; only the internal sampling schedule is accelerated.
-/
noncomputable def normalize
    (s : MulCauchyStream) :
    MulCauchyStream where

  term :=
    fun n =>
      s.term (normalizationStage s n)

  cauchy := by
    intro level

    refine ⟨level, ?_⟩
    intro m n hm hn

    exact
      scaleAnchor_spec s level
        (normalizationStage s m)
        (normalizationStage s n)
        (scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
          s hm)
        (scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
          s hn)

@[simp] theorem normalize_term
    (s : MulCauchyStream)
    (n : Depth) :
    (normalize s).term n =
      s.term (normalizationStage s n) := rfl

/--
Universal modulus of the normalized stream: the requested scale itself is a
valid tail anchor.
-/
theorem normalize_scaleWithin
    (s : MulCauchyStream)
    (level m n : Depth)
    (hm : Depth.AtOrAfter level m)
    (hn : Depth.AtOrAfter level n) :
    MulRat.ScaleWithin level
      ((normalize s).term m)
      ((normalize s).term n) := by

  exact
    scaleAnchor_spec s level
      (normalizationStage s m)
      (normalizationStage s n)
      (scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
        s hm)
      (scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
        s hn)

/--
Rate normalization does not change the represented completed point.
-/
theorem normalize_asymptotic
    (s : MulCauchyStream) :
    MulAsymptotic (normalize s) s := by

  intro level

  let anchor :=
    Depth.join
      (scaleAnchor s level)
      level

  refine ⟨anchor, ?_⟩
  intro n hn

  have hnAnchor :
      Depth.AtOrAfter
        (scaleAnchor s level)
        n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        (scaleAnchor s level)
        level)
      hn

  have hnLevel :
      Depth.AtOrAfter level n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        (scaleAnchor s level)
        level)
      hn

  have hnormAnchor :
      Depth.AtOrAfter
        (scaleAnchor s level)
        (normalizationStage s n) :=
    scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
      s hnLevel

  exact
    scaleAnchor_spec s level
      (normalizationStage s n)
      n
      hnormAnchor
      hnAnchor

/-- Rate normalization preserves the quotient value exactly. -/
theorem ofStream_normalize
    (s : MulCauchyStream) :
    MulReal.ofStream (normalize s) =
      MulReal.ofStream s := by

  apply MulReal.ofStream_eq_of_asymptotic
  exact normalize_asymptotic s

end MulCauchyStream

namespace StreamFiniteMulCoupling

/--
Normalize the convergence rate of every canonical finite-output stream.

This deliberately does not claim the old exact *termwise* bilinear laws:
different finite input pairs may receive different accelerated schedules.
Their quotient values, however, are unchanged.
-/
noncomputable def rateNormalized
    (C : StreamFiniteMulCoupling) :
    StreamFiniteMulCoupling where

  realize :=
    fun a b =>
      MulCauchyStream.normalize
        (C.realize a b)

/--
Every rate-normalized finite realizer has a global, input-independent internal
Cauchy modulus.
-/
theorem rateNormalized_output_cauchy
    (C : StreamFiniteMulCoupling)
    (level : Depth) :
    ∃ anchor : Depth,
      ∀ a b : MulRat,
        ∀ m n : Depth,
          Depth.AtOrAfter anchor m →
          Depth.AtOrAfter anchor n →
          MulRat.ScaleWithin level
            (((C.rateNormalized).realize a b).term m)
            (((C.rateNormalized).realize a b).term n) := by

  refine ⟨level, ?_⟩
  intro a b m n hm hn

  exact
    MulCauchyStream.normalize_scaleWithin
      (C.realize a b)
      level m n hm hn

/--
Rate normalization preserves whatever finite quotient coupling the original
stream realizer represented.
-/
theorem rateNormalized_realizesFinite
    (C : StreamFiniteMulCoupling)
    (F : FiniteMulCoupling)
    (hRealize : RealizesFiniteCoupling C F) :
    RealizesFiniteCoupling
      C.rateNormalized F := by

  intro a b

  change
    MulReal.ofStream
        (MulCauchyStream.normalize
          (C.realize a b)) =
      F.couple a b

  rw [MulCauchyStream.ofStream_normalize]

  exact hRealize a b

end StreamFiniteMulCoupling

end PrimeTensor
