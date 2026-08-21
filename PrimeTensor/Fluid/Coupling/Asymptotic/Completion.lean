import PrimeTensor.Fluid.Coupling.Asymptotic
import PrimeTensor.Analysis.Control

/-!
# Completion algebra from normalized asymptotic laws

Rate normalization deliberately destroys exact termwise bilinearity: different
finite input pairs may be accelerated by different schedules.  The quotient
algebra remains exact, and `CouplingAsymptotic` recovers the corresponding
stream laws up to `MulAsymptotic`.

A remaining issue is diagonal sampling.  For a fixed finite triple, an
asymptotic law may begin only after a triple-dependent internal anchor, while
the completed diagonal samples the internal output at the current external
index.

The universal output modulus supplied by rate normalization removes this last
rate mismatch.

Given asymptotic streams `s ~ t`, if the finite-output streams can move between
any two internal stages at a scale determined only by those stages, then a
diagonal sample at stage `n` may be compared to an arbitrarily late witness
`k`:

    s(n)  ~  s(k)  ~  t(k)  ~  t(n).

The witness `k` may depend on the finite values at `n`; the required lower
bound on `n` does not.

This file uses that synchronization mechanism to prove the completed unit and
bilinear laws from:

* completion stability (existence and representative independence);
* universal normalized output rate;
* finite algebra laws up to `MulAsymptotic`.

No conventional real bridge is used.
-/

namespace PrimeTensor

/--
Every finite-output stream has the native normalization modulus with no
input-dependent anchor: scale `level` itself is a valid internal tail anchor.
-/
def HasUniversalOutputRate
    (C : StreamFiniteMulCoupling) : Prop :=
  ∀ (level : Depth) (a b : MulRat) (m n : Depth),
    Depth.AtOrAfter level m →
    Depth.AtOrAfter level n →
    MulRat.ScaleWithin level
      ((C.realize a b).term m)
      ((C.realize a b).term n)

namespace StreamFiniteMulCoupling

/--
Rate normalization gives the universal output rate by construction.
-/
theorem rateNormalized_hasUniversalOutputRate
    (C : StreamFiniteMulCoupling) :
    HasUniversalOutputRate C.rateNormalized := by

  intro level a b m n hm hn

  exact
    MulCauchyStream.normalize_scaleWithin
      (C.realize a b)
      level m n hm hn

/--
Synchronize one asymptotic finite-output law against the constant pivot at a
diagonal sample.

The asymptotic witness may begin arbitrarily late.  We move the current sample
and the witness into one common late internal stage, using the universal output
rate for the nonconstant side.
-/
theorem sample_asymptotic_one
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    {a b : MulRat}
    (h :
      MulAsymptotic
        (C.realize a b)
        (MulCauchyStream.constant 1))
    (level n : Depth)
    (hn : Depth.AtOrAfter (.succ level) n) :
    MulRat.ScaleWithin level
      ((C.realize a b).term n)
      1 := by

  obtain ⟨asymAnchor, hAsym⟩ :=
    h (.succ level)

  let k :=
    Depth.join asymAnchor (.succ level)

  have hkAsym :
      Depth.AtOrAfter asymAnchor k := by
    exact
      Depth.left_atOrAfter
        asymAnchor (.succ level)

  have hkFine :
      Depth.AtOrAfter (.succ level) k := by
    exact
      Depth.right_atOrAfter
        asymAnchor (.succ level)

  have hMove :
      MulRat.ScaleWithin (.succ level)
        ((C.realize a b).term n)
        ((C.realize a b).term k) := by
    exact
      hRate
        (.succ level)
        a b n k
        hn hkFine

  have hMeet :
      MulRat.ScaleWithin (.succ level)
        ((C.realize a b).term k)
        1 := by

    have hk := hAsym k hkAsym

    simpa only [
      MulCauchyStream.constant_term
    ] using hk

  exact
    MulRat.scaleWithin_comp
      hMove hMeet

/--
Synchronize an asymptotic multiplicative law at one diagonal sample.

There are three comparison legs:

    source(n) -> source(k)
    source(k) -> product(k)
    product(k) -> product(n).

Two extra refinement levels compose the three legs.  A third successor in the
external anchor supplies the one-finer input needed by `scaleWithin_mul` on the
product leg.
-/
theorem sample_asymptotic_mul
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    {sourceA sourceB leftA leftB rightA rightB : MulRat}
    (h :
      MulAsymptotic
        (C.realize sourceA sourceB)
        (
          MulCauchyStream.mul
            (C.realize leftA leftB)
            (C.realize rightA rightB)
        ))
    (level n : Depth)
    (hn :
      Depth.AtOrAfter
        (.succ (.succ (.succ level)))
        n) :
    MulRat.ScaleWithin level
      ((C.realize sourceA sourceB).term n)
      (
        (C.realize leftA leftB).term n *
          (C.realize rightA rightB).term n
      ) := by

  let fine : Depth :=
    .succ (.succ level)

  let productFine : Depth :=
    .succ fine

  have hFineProductFine :
      Depth.AtOrAfter fine productFine := by
    exact
      Depth.AtOrAfter.later
        (Depth.AtOrAfter.here fine)

  have hnProductFine :
      Depth.AtOrAfter productFine n := by
    simpa only [productFine, fine] using hn

  have hnFine :
      Depth.AtOrAfter fine n :=
    Depth.atOrAfter_trans
      hFineProductFine
      hnProductFine

  obtain ⟨asymAnchor, hAsym⟩ :=
    h fine

  let k :=
    Depth.join asymAnchor productFine

  have hkAsym :
      Depth.AtOrAfter asymAnchor k := by
    exact
      Depth.left_atOrAfter
        asymAnchor productFine

  have hkProductFine :
      Depth.AtOrAfter productFine k := by
    exact
      Depth.right_atOrAfter
        asymAnchor productFine

  have hkFine :
      Depth.AtOrAfter fine k :=
    Depth.atOrAfter_trans
      hFineProductFine
      hkProductFine

  have hSourceMove :
      MulRat.ScaleWithin fine
        ((C.realize sourceA sourceB).term n)
        ((C.realize sourceA sourceB).term k) := by

    exact
      hRate
        fine
        sourceA sourceB
        n k
        hnFine hkFine

  have hMeet :
      MulRat.ScaleWithin fine
        ((C.realize sourceA sourceB).term k)
        (
          (C.realize leftA leftB).term k *
            (C.realize rightA rightB).term k
        ) := by

    have hk := hAsym k hkAsym

    simpa only [
      MulCauchyStream.mul_term
    ] using hk

  have hLeftMove :
      MulRat.ScaleWithin productFine
        ((C.realize leftA leftB).term k)
        ((C.realize leftA leftB).term n) := by

    exact
      hRate
        productFine
        leftA leftB
        k n
        hkProductFine hnProductFine

  have hRightMove :
      MulRat.ScaleWithin productFine
        ((C.realize rightA rightB).term k)
        ((C.realize rightA rightB).term n) := by

    exact
      hRate
        productFine
        rightA rightB
        k n
        hkProductFine hnProductFine

  have hProductMove :
      MulRat.ScaleWithin fine
        (
          (C.realize leftA leftB).term k *
            (C.realize rightA rightB).term k
        )
        (
          (C.realize leftA leftB).term n *
            (C.realize rightA rightB).term n
        ) := by

    simpa only [productFine] using
      (MulRat.scaleWithin_mul
        hLeftMove hRightMove)

  have hFirstTwo :
      MulRat.ScaleWithin (.succ level)
        ((C.realize sourceA sourceB).term n)
        (
          (C.realize leftA leftB).term k *
            (C.realize rightA rightB).term k
        ) := by

    simpa only [fine] using
      (MulRat.scaleWithin_comp
        hSourceMove hMeet)

  have hProductMoveWeak :
      MulRat.ScaleWithin (.succ level)
        (
          (C.realize leftA leftB).term k *
            (C.realize rightA rightB).term k
        )
        (
          (C.realize leftA leftB).term n *
            (C.realize rightA rightB).term n
        ) := by

    simpa only [fine] using
      (MulRat.scaleWithin_succ_weaken
        hProductMove)

  exact
    MulRat.scaleWithin_comp
      hFirstTwo
      hProductMoveWeak

/--
Completed left-unit law from asymptotic finite lawfulness plus universal rate.
-/
theorem complete_one_left_of_asymptotic
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hAlg : IsAsymptoticStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (b : MulReal) :
    (C.complete hC).couple 1 b = 1 := by

  refine Quotient.inductionOn b ?_
  intro y

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          (MulCauchyStream.constant 1) y) =
      MulReal.ofStream
        (MulCauchyStream.constant 1)

  apply MulReal.ofStream_eq_of_asymptotic

  intro level

  refine ⟨.succ level, ?_⟩
  intro n hn

  change
    MulRat.ScaleWithin level
      ((C.realize 1 (y.term n)).term n)
      1

  exact
    C.sample_asymptotic_one
      hRate
      (hAlg.one_left (y.term n))
      level n hn

/--
Completed right-unit law from asymptotic finite lawfulness plus universal rate.
-/
theorem complete_one_right_of_asymptotic
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hAlg : IsAsymptoticStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C)
    (a : MulReal) :
    (C.complete hC).couple a 1 = 1 := by

  refine Quotient.inductionOn a ?_
  intro x

  change
    MulReal.ofStream
        (C.diagonal hC.diagonal_cauchy
          x (MulCauchyStream.constant 1)) =
      MulReal.ofStream
        (MulCauchyStream.constant 1)

  apply MulReal.ofStream_eq_of_asymptotic

  intro level

  refine ⟨.succ level, ?_⟩
  intro n hn

  change
    MulRat.ScaleWithin level
      ((C.realize (x.term n) 1).term n)
      1

  exact
    C.sample_asymptotic_one
      hRate
      (hAlg.one_right (x.term n))
      level n hn

/--
Completed multiplicativity in the first slot from asymptotic finite lawfulness
plus universal rate.
-/
theorem complete_mul_left_of_asymptotic
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hAlg : IsAsymptoticStreamFiniteMulCoupling C)
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
        (
          MulCauchyStream.mul
            (C.diagonal hC.diagonal_cauchy x z)
            (C.diagonal hC.diagonal_cauchy y z)
        )

  apply MulReal.ofStream_eq_of_asymptotic

  intro level

  refine
    ⟨.succ (.succ (.succ level)), ?_⟩

  intro n hn

  change
    MulRat.ScaleWithin level
      (
        (C.realize
          (x.term n * y.term n)
          (z.term n)).term n
      )
      (
        (C.realize (x.term n) (z.term n)).term n *
          (C.realize (y.term n) (z.term n)).term n
      )

  exact
    C.sample_asymptotic_mul
      hRate
      (hAlg.mul_left
        (x.term n)
        (y.term n)
        (z.term n))
      level n hn

/--
Completed multiplicativity in the second slot from asymptotic finite lawfulness
plus universal rate.
-/
theorem complete_mul_right_of_asymptotic
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hAlg : IsAsymptoticStreamFiniteMulCoupling C)
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
        (
          MulCauchyStream.mul
            (C.diagonal hC.diagonal_cauchy x y)
            (C.diagonal hC.diagonal_cauchy x z)
        )

  apply MulReal.ofStream_eq_of_asymptotic

  intro level

  refine
    ⟨.succ (.succ (.succ level)), ?_⟩

  intro n hn

  change
    MulRat.ScaleWithin level
      (
        (C.realize
          (x.term n)
          (y.term n * z.term n)).term n
      )
      (
        (C.realize (x.term n) (y.term n)).term n *
          (C.realize (x.term n) (z.term n)).term n
      )

  exact
    C.sample_asymptotic_mul
      hRate
      (hAlg.mul_right
        (x.term n)
        (y.term n)
        (z.term n))
      level n hn

/--
A completion-stable realizer with universal output rate and asymptotic finite
algebra laws produces a lawful coupling on all completed inputs.

This is the replacement for the old theorem whose algebra hypothesis required
exact termwise bilinearity.
-/
theorem complete_lawful_of_asymptotic
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hAlg : IsAsymptoticStreamFiniteMulCoupling C)
    (hC : IsCouplingCompletionStable C) :
    IsMulCoupling (C.complete hC) where

  couple_one_left :=
    C.complete_one_left_of_asymptotic
      hRate hAlg hC

  couple_one_right :=
    C.complete_one_right_of_asymptotic
      hRate hAlg hC

  couple_mul_left :=
    C.complete_mul_left_of_asymptotic
      hRate hAlg hC

  couple_mul_right :=
    C.complete_mul_right_of_asymptotic
      hRate hAlg hC

end StreamFiniteMulCoupling

end PrimeTensor
