import PrimeTensor.Fluid.CouplingAsymptoticCompletion

/-!
# Tail-local input control after rate normalization

The old `CouplingTailScaleControl` mixed two logically different obligations:

* output convergence in the internal approximation stage;
* local continuity with respect to finite inputs along two fixed Cauchy tails.

The first obligation was the source of the same-depth scheduling failure for the
raw concrete kernel.  Rate normalization repairs it universally.

This file therefore isolates only the surviving analytic content: tail-local
input continuity.

For fixed input streams `a` and `b`, sufficiently late finite values from those
tails have a local two-input continuity modulus.  Unlike
`CouplingUniformScaleControl`, the modulus may depend on the two input streams,
which is essential for couplings such as

    exp (log a * log b)

whose sensitivity is not globally bounded over all positive inputs.

The main results are:

1. tail-local input control passes from a raw stream realizer to its
   rate-normalized realizer;
2. universal normalized output rate plus tail-local input control implies full
   `IsCouplingCompletionStable`;
3. consequently, rate normalization reduces completion stability to tail-local
   input continuity of the original finite realizer.

No conventional real bridge is used.
-/

namespace PrimeTensor

/--
Local two-input scale control along fixed Cauchy tails.

This is exactly the `input_control` half of the old
`CouplingTailScaleControl`, separated from any claim about the raw output
convergence rate.
-/
structure CouplingTailInputScaleControl
    (C : StreamFiniteMulCoupling) : Prop where

  input_control :
    ∀ (a b : MulCauchyStream) (target : Depth),
      ∃ sourceA sourceB anchor : Depth,
        ∀ m n : Depth,
          Depth.AtOrAfter anchor m →
          Depth.AtOrAfter anchor n →
          ∀ a' b' : MulRat,
            MulRat.ScaleWithin sourceA
              (a.term m) a' →
            MulRat.ScaleWithin sourceB
              (b.term m) b' →
            MulRat.ScaleWithin target
              ((C.realize
                (a.term m)
                (b.term m)).term n)
              ((C.realize a' b').term n)

namespace CouplingTailInputScaleControl

variable {C : StreamFiniteMulCoupling}

/--
Rate normalization preserves tail-local input continuity.

The two normalized output streams may use different internal schedules.  Move
both normalized samples to one common raw stage `k`, apply the raw input
continuity estimate there, then move back.

The stage `k` may depend on the two finite input pairs.  The external tail
anchor does not.
-/
theorem rateNormalized
    (hC : CouplingTailInputScaleControl C) :
    CouplingTailInputScaleControl C.rateNormalized := by

  constructor

  intro a b target

  let fine : Depth :=
    .succ (.succ target)

  obtain
    ⟨sourceA, sourceB, rawAnchor, hInput⟩ :=
      hC.input_control a b fine

  let anchor :=
    Depth.join rawAnchor fine

  refine
    ⟨sourceA, sourceB, anchor, ?_⟩

  intro m n hm hn a' b' ha hb

  have hmRaw :
      Depth.AtOrAfter rawAnchor m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter rawAnchor fine)
      hm

  have hnFine :
      Depth.AtOrAfter fine n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter rawAnchor fine)
      hn

  let s₁ : MulCauchyStream :=
    C.realize (a.term m) (b.term m)

  let s₂ : MulCauchyStream :=
    C.realize a' b'

  let k :=
    Depth.join3
      rawAnchor
      (MulCauchyStream.scaleAnchor s₁ fine)
      (MulCauchyStream.scaleAnchor s₂ fine)

  have hkRaw :
      Depth.AtOrAfter rawAnchor k := by
    exact
      Depth.first_atOrAfter_join3
        rawAnchor
        (MulCauchyStream.scaleAnchor s₁ fine)
        (MulCauchyStream.scaleAnchor s₂ fine)

  have hk₁ :
      Depth.AtOrAfter
        (MulCauchyStream.scaleAnchor s₁ fine)
        k := by
    exact
      Depth.second_atOrAfter_join3
        rawAnchor
        (MulCauchyStream.scaleAnchor s₁ fine)
        (MulCauchyStream.scaleAnchor s₂ fine)

  have hk₂ :
      Depth.AtOrAfter
        (MulCauchyStream.scaleAnchor s₂ fine)
        k := by
    exact
      Depth.third_atOrAfter_join3
        rawAnchor
        (MulCauchyStream.scaleAnchor s₁ fine)
        (MulCauchyStream.scaleAnchor s₂ fine)

  have hn₁ :
      Depth.AtOrAfter
        (MulCauchyStream.scaleAnchor s₁ fine)
        (MulCauchyStream.normalizationStage s₁ n) := by
    exact
      MulCauchyStream.scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
        s₁ hnFine

  have hn₂ :
      Depth.AtOrAfter
        (MulCauchyStream.scaleAnchor s₂ fine)
        (MulCauchyStream.normalizationStage s₂ n) := by
    exact
      MulCauchyStream.scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
        s₂ hnFine

  have hMove₁ :
      MulRat.ScaleWithin fine
        ((C.rateNormalized.realize
          (a.term m)
          (b.term m)).term n)
        (s₁.term k) := by

    change
      MulRat.ScaleWithin fine
        (s₁.term
          (MulCauchyStream.normalizationStage s₁ n))
        (s₁.term k)

    exact
      MulCauchyStream.scaleAnchor_spec
        s₁ fine
        (MulCauchyStream.normalizationStage s₁ n)
        k
        hn₁ hk₁

  have hInputLeg :
      MulRat.ScaleWithin fine
        (s₁.term k)
        (s₂.term k) := by

    change
      MulRat.ScaleWithin fine
        ((C.realize
          (a.term m)
          (b.term m)).term k)
        ((C.realize a' b').term k)

    exact
      hInput
        m k
        hmRaw hkRaw
        a' b'
        ha hb

  have hMove₂ :
      MulRat.ScaleWithin fine
        (s₂.term k)
        ((C.rateNormalized.realize a' b').term n) := by

    change
      MulRat.ScaleWithin fine
        (s₂.term k)
        (s₂.term
          (MulCauchyStream.normalizationStage s₂ n))

    exact
      MulCauchyStream.scaleAnchor_spec
        s₂ fine
        k
        (MulCauchyStream.normalizationStage s₂ n)
        hk₂ hn₂

  have hFirstTwo :
      MulRat.ScaleWithin (.succ target)
        ((C.rateNormalized.realize
          (a.term m)
          (b.term m)).term n)
        (s₂.term k) := by

    simpa only [fine] using
      (MulRat.scaleWithin_comp
        hMove₁ hInputLeg)

  have hMove₂Weak :
      MulRat.ScaleWithin (.succ target)
        (s₂.term k)
        ((C.rateNormalized.realize a' b').term n) := by

    simpa only [fine] using
      (MulRat.scaleWithin_succ_weaken
        hMove₂)

  exact
    MulRat.scaleWithin_comp
      hFirstTwo hMove₂Weak

end CouplingTailInputScaleControl

namespace StreamFiniteMulCoupling

/--
Universal output rate plus tail-local input continuity makes every diagonal
Cauchy.
-/
theorem diagonalCauchy_of_tailInputControl
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hInput : CouplingTailInputScaleControl C) :
    C.DiagonalCauchy := by

  intro a b level

  obtain
    ⟨sourceA, sourceB, inputAnchor, hControl⟩ :=
      hInput.input_control a b (.succ level)

  obtain ⟨aAnchor, ha⟩ :=
    a.cauchy sourceA

  obtain ⟨bAnchor, hb⟩ :=
    b.cauchy sourceB

  let inputTail :=
    Depth.join3
      inputAnchor aAnchor bAnchor

  let anchor :=
    Depth.join (.succ level) inputTail

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  have hmFine :
      Depth.AtOrAfter (.succ level) m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        (.succ level) inputTail)
      hm

  have hnFine :
      Depth.AtOrAfter (.succ level) n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        (.succ level) inputTail)
      hn

  have hmTail :
      Depth.AtOrAfter inputTail m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        (.succ level) inputTail)
      hm

  have hnTail :
      Depth.AtOrAfter inputTail n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        (.succ level) inputTail)
      hn

  have hmInput :
      Depth.AtOrAfter inputAnchor m :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hmTail

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hnTail

  have hmA :
      Depth.AtOrAfter aAnchor m :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hmTail

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hnTail

  have hmB :
      Depth.AtOrAfter bAnchor m :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hmTail

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hnTail

  have hStage :
      MulRat.ScaleWithin (.succ level)
        ((C.realize
          (a.term m)
          (b.term m)).term m)
        ((C.realize
          (a.term m)
          (b.term m)).term n) := by

    exact
      hRate
        (.succ level)
        (a.term m)
        (b.term m)
        m n
        hmFine hnFine

  have hInputs :
      MulRat.ScaleWithin (.succ level)
        ((C.realize
          (a.term m)
          (b.term m)).term n)
        ((C.realize
          (a.term n)
          (b.term n)).term n) := by

    exact
      hControl
        m n
        hmInput hnInput
        (a.term n)
        (b.term n)
        (ha m n hmA hnA)
        (hb m n hmB hnB)

  exact
    MulRat.scaleWithin_comp
      hStage hInputs

/--
Tail-local input continuity makes diagonalization independent of asymptotically
equivalent input representatives.
-/
theorem diagonalAsymptotic_of_tailInputControl
    (C : StreamFiniteMulCoupling)
    (hInput : CouplingTailInputScaleControl C)
    (hCauchy : C.DiagonalCauchy)
    {a a' b b' : MulCauchyStream}
    (ha : MulAsymptotic a a')
    (hb : MulAsymptotic b b') :
    MulAsymptotic
      (C.diagonal hCauchy a b)
      (C.diagonal hCauchy a' b') := by

  intro level

  obtain
    ⟨sourceA, sourceB, inputAnchor, hControl⟩ :=
      hInput.input_control a b level

  obtain ⟨aAnchor, haTail⟩ :=
    ha sourceA

  obtain ⟨bAnchor, hbTail⟩ :=
    hb sourceB

  let anchor :=
    Depth.join3
      inputAnchor aAnchor bAnchor

  refine ⟨anchor, ?_⟩
  intro n hn

  have hnInput :
      Depth.AtOrAfter inputAnchor n :=
    Depth.atOrAfter_trans
      (Depth.first_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.second_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hn

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.third_atOrAfter_join3
        inputAnchor aAnchor bAnchor)
      hn

  change
    MulRat.ScaleWithin level
      ((C.realize
        (a.term n)
        (b.term n)).term n)
      ((C.realize
        (a'.term n)
        (b'.term n)).term n)

  exact
    hControl
      n n
      hnInput hnInput
      (a'.term n)
      (b'.term n)
      (haTail n hnA)
      (hbTail n hnB)

/--
Universal output rate and tail-local input continuity imply the exact
completion-stability structure required by quotient lifting.
-/
theorem toCompletionStable_of_tailInputControl
    (C : StreamFiniteMulCoupling)
    (hRate : HasUniversalOutputRate C)
    (hInput : CouplingTailInputScaleControl C) :
    IsCouplingCompletionStable C := by

  let hCauchy : C.DiagonalCauchy :=
    C.diagonalCauchy_of_tailInputControl
      hRate hInput

  refine
    {
      diagonal_cauchy := hCauchy
      diagonal_asymptotic := ?_
    }

  intro a a' b b' ha hb

  exact
    C.diagonalAsymptotic_of_tailInputControl
      hInput hCauchy ha hb

/--
For a raw realizer, tail-local input continuity alone is enough after rate
normalization: normalization supplies the universal output rate automatically.
-/
theorem rateNormalized_toCompletionStable_of_tailInputControl
    (C : StreamFiniteMulCoupling)
    (hInput : CouplingTailInputScaleControl C) :
    IsCouplingCompletionStable C.rateNormalized := by

  exact
    C.rateNormalized.toCompletionStable_of_tailInputControl
      C.rateNormalized_hasUniversalOutputRate
      hInput.rateNormalized

end StreamFiniteMulCoupling

end PrimeTensor
