import PrimeTensor.Fluid.CouplingAsymptoticCompletion

/-!
# Sequential input control for coupling completion

`CouplingTailInputScaleControl` is a useful sufficient criterion, but it still
quantifies over arbitrary finite perturbations near a tail value.  For the
concrete log-product approximation this is stronger than diagonal completion
actually requires, and may reintroduce the same high-complexity rational
pathology that motivated rate normalization.

The diagonal construction uses only two kinds of input comparisons:

1. two actual positions `m,n` of the same pair of Cauchy input streams;
2. the same position `n` in two asymptotically equivalent choices of input
   representatives.

This file isolates exactly those comparisons.

Together with the universal internal-output rate supplied by normalization,
these two sequential control laws imply full `IsCouplingCompletionStable`.

No arbitrary nearby `MulRat` is quantified over.
No conventional real bridge is used.
-/

namespace PrimeTensor

/--
Exactly the finite-input continuity needed by diagonal completion.

`cauchy_input` controls motion along two fixed Cauchy input sequences.

`representative_input` controls pointwise replacement by asymptotically
equivalent input representatives.
-/
structure CouplingSequentialScaleControl
    (C : StreamFiniteMulCoupling) : Prop where

  cauchy_input :
    ∀ (a b : MulCauchyStream) (target : Depth),
      ∃ anchor : Depth,
        ∀ m n : Depth,
          Depth.AtOrAfter anchor m →
          Depth.AtOrAfter anchor n →
          MulRat.ScaleWithin target
            (
              (C.realize
                (a.term m)
                (b.term m)).term n
            )
            (
              (C.realize
                (a.term n)
                (b.term n)).term n
            )

  representative_input :
    ∀ {a a' b b' : MulCauchyStream},
      MulAsymptotic a a' →
      MulAsymptotic b b' →
      ∀ target : Depth,
        ∃ anchor : Depth,
          ∀ n : Depth,
            Depth.AtOrAfter anchor n →
            MulRat.ScaleWithin target
              (
                (C.realize
                  (a.term n)
                  (b.term n)).term n
              )
              (
                (C.realize
                  (a'.term n)
                  (b'.term n)).term n
              )

namespace StreamFiniteMulCoupling

/--
Universal output rate plus sequential input control makes every diagonal
intrinsically Cauchy.

The two comparison legs are exactly

    C(a_m,b_m)[m]
      ~ C(a_m,b_m)[n]
      ~ C(a_n,b_n)[n].

The first is universal output-rate control.  The second is the sequential
finite-input law.
-/
theorem diagonalCauchy_of_sequentialControl
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hSeq : CouplingSequentialScaleControl C) :
    C.DiagonalCauchy := by

  intro a b level

  obtain ⟨inputAnchor, hInput⟩ :=
    hSeq.cauchy_input a b (.succ level)

  let anchor :=
    Depth.join (.succ level) inputAnchor

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  have hmFine :
      Depth.AtOrAfter (.succ level) m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        (.succ level) inputAnchor)
      hm

  have hnFine :
      Depth.AtOrAfter (.succ level) n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        (.succ level) inputAnchor)
      hn

  have hmInput :
      Depth.AtOrAfter inputAnchor m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        (.succ level) inputAnchor)
      hm

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        (.succ level) inputAnchor)
      hn

  have hStage :
      MulRat.ScaleWithin (.succ level)
        (
          (C.realize
            (a.term m)
            (b.term m)).term m
        )
        (
          (C.realize
            (a.term m)
            (b.term m)).term n
        ) := by

    exact
      hRate
        (.succ level)
        (a.term m)
        (b.term m)
        m n
        hmFine hnFine

  have hInputs :
      MulRat.ScaleWithin (.succ level)
        (
          (C.realize
            (a.term m)
            (b.term m)).term n
        )
        (
          (C.realize
            (a.term n)
            (b.term n)).term n
        ) := by

    exact
      hInput
        m n
        hmInput hnInput

  exact
    MulRat.scaleWithin_comp
      hStage hInputs

/--
Sequential representative control is exactly the second completion obligation:
diagonalization respects asymptotically equivalent input streams.
-/
theorem diagonalAsymptotic_of_sequentialControl
    (C : StreamFiniteMulCoupling)
    (hSeq : CouplingSequentialScaleControl C)
    (hCauchy : C.DiagonalCauchy)
    {a a' b b' : MulCauchyStream}
    (ha : MulAsymptotic a a')
    (hb : MulAsymptotic b b') :
    MulAsymptotic
      (C.diagonal hCauchy a b)
      (C.diagonal hCauchy a' b') := by

  intro level

  obtain ⟨anchor, hInput⟩ :=
    hSeq.representative_input
      ha hb level

  refine ⟨anchor, ?_⟩
  intro n hn

  change
    MulRat.ScaleWithin level
      (
        (C.realize
          (a.term n)
          (b.term n)).term n
      )
      (
        (C.realize
          (a'.term n)
          (b'.term n)).term n
      )

  exact
    hInput n hn

/--
The exact completion-stability structure follows from universal internal output
rate and the two sequence-level finite-input control laws.
-/
theorem toCompletionStable_of_sequentialControl
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hSeq : CouplingSequentialScaleControl C) :
    IsCouplingCompletionStable C := by

  let hCauchy : C.DiagonalCauchy :=
    C.diagonalCauchy_of_sequentialControl
      hRate hSeq

  refine
    {
      diagonal_cauchy := hCauchy
      diagonal_asymptotic := ?_
    }

  intro a a' b b' ha hb

  exact
    C.diagonalAsymptotic_of_sequentialControl
      hSeq hCauchy ha hb

/--
For a rate-normalized realizer, sequential input control alone implies
completion stability because normalization already supplies universal output
rate.
-/
theorem rateNormalized_completionStable_of_sequentialControl
    (C : StreamFiniteMulCoupling)
    (hSeq :
      CouplingSequentialScaleControl
        C.rateNormalized) :
    IsCouplingCompletionStable
      C.rateNormalized := by

  exact
    C.rateNormalized.toCompletionStable_of_sequentialControl
      C.rateNormalized_hasUniversalOutputRate
      hSeq

end StreamFiniteMulCoupling

end PrimeTensor
