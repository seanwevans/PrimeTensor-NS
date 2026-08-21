import PrimeTensor.Bridge.LogCauchy
import PrimeTensor.Bridge.FiniteSemantics

/-!
# Real sequence calculus over native depth tails

This is a bridge-only theorem layer.

PrimeTensor intentionally uses `Depth.AtOrAfter` rather than installing an
ordinary additive/order-theoretic indexing model on native `Depth`.  We keep
that boundary intact and develop only the small amount of conventional real
sequence calculus needed for the concrete log-product semantics.

The main facts are:

* an ordinary real Cauchy tail over `Depth.AtOrAfter` is eventually bounded;
* products of two such Cauchy tails are Cauchy;
* pointwise products respect asymptotically equivalent Cauchy tails;
* therefore the logarithm of the finite semantic target

      exp (log a * log b)

  is Cauchy along intrinsic input streams and respects intrinsic asymptotic
  replacement of those streams.

No additive operation is added to the native object language.
-/

namespace PrimeTensor
namespace Bridge

/--
Bridge-only Cauchy condition for an ordinary real-valued function indexed by
native positive depth.
-/
def DepthRealCauchy
    (f : Depth → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ m n : Depth,
        Depth.AtOrAfter anchor m →
        Depth.AtOrAfter anchor n →
        abs (f m - f n) < ε

/--
Bridge-only asymptotic equivalence for ordinary real-valued functions indexed
by native positive depth.
-/
def DepthRealAsymptotic
    (f g : Depth → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        abs (f n - g n) < ε

/--
Every real Cauchy tail is eventually bounded in absolute value.
-/
theorem DepthRealCauchy.eventually_abs_lt
    {f : Depth → ℝ}
    (hf : DepthRealCauchy f) :
    ∃ B : ℝ,
      0 < B ∧
      ∃ anchor : Depth,
        ∀ n : Depth,
          Depth.AtOrAfter anchor n →
          abs (f n) < B := by

  obtain ⟨anchor, hTail⟩ :=
    hf 1 (by norm_num)

  let B : ℝ :=
    1 + abs (f anchor)

  refine ⟨B, ?_, anchor, ?_⟩

  · dsimp [B]
    nlinarith [abs_nonneg (f anchor)]

  · intro n hn

    have hClose :
        abs (f n - f anchor) < 1 :=
      hTail
        n anchor
        hn
        (Depth.AtOrAfter.here anchor)

    calc
      abs (f n)
          =
        abs
          (
            (f n - f anchor) +
              f anchor
          ) := by
            congr 1
            ring

      _ ≤
        abs (f n - f anchor) +
          abs (f anchor) :=
        abs_add_le _ _

      _ <
        1 + abs (f anchor) := by
          simpa only [add_comm] using
            (add_lt_add_right
              hClose
              (abs (f anchor)))

      _ = B := by
        rfl

/--
Products of real Cauchy tails are Cauchy.
-/
theorem DepthRealCauchy.mul
    {f g : Depth → ℝ}
    (hf : DepthRealCauchy f)
    (hg : DepthRealCauchy g) :
    DepthRealCauchy
      (fun n => f n * g n) := by

  intro ε hε

  obtain ⟨Bf, hBf, fBoundAnchor, hfBound⟩ :=
    hf.eventually_abs_lt

  obtain ⟨Bg, hBg, gBoundAnchor, hgBound⟩ :=
    hg.eventually_abs_lt

  let D : ℝ :=
    Bf + Bg

  have hD :
      0 < D := by
    dsimp [D]
    nlinarith

  let δ : ℝ :=
    ε / D

  have hδ :
      0 < δ := by
    dsimp [δ]
    exact div_pos hε hD

  obtain ⟨fCloseAnchor, hfClose⟩ :=
    hf δ hδ

  obtain ⟨gCloseAnchor, hgClose⟩ :=
    hg δ hδ

  let closeTail :=
    Depth.join fCloseAnchor gCloseAnchor

  let boundTail :=
    Depth.join fBoundAnchor gBoundAnchor

  let anchor :=
    Depth.join boundTail closeTail

  refine ⟨anchor, ?_⟩
  intro m n hm hn

  have hmBoundTail :
      Depth.AtOrAfter boundTail m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter boundTail closeTail)
      hm

  have hnBoundTail :
      Depth.AtOrAfter boundTail n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter boundTail closeTail)
      hn

  have hmCloseTail :
      Depth.AtOrAfter closeTail m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter boundTail closeTail)
      hm

  have hnCloseTail :
      Depth.AtOrAfter closeTail n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter boundTail closeTail)
      hn

  have hmFBound :
      Depth.AtOrAfter fBoundAnchor m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        fBoundAnchor gBoundAnchor)
      hmBoundTail

  have hnGBound :
      Depth.AtOrAfter gBoundAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        fBoundAnchor gBoundAnchor)
      hnBoundTail

  have hmFClose :
      Depth.AtOrAfter fCloseAnchor m :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        fCloseAnchor gCloseAnchor)
      hmCloseTail

  have hnFClose :
      Depth.AtOrAfter fCloseAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        fCloseAnchor gCloseAnchor)
      hnCloseTail

  have hmGClose :
      Depth.AtOrAfter gCloseAnchor m :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        fCloseAnchor gCloseAnchor)
      hmCloseTail

  have hnGClose :
      Depth.AtOrAfter gCloseAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        fCloseAnchor gCloseAnchor)
      hnCloseTail

  have hfm :
      abs (f m) < Bf :=
    hfBound m hmFBound

  have hgn :
      abs (g n) < Bg :=
    hgBound n hnGBound

  have hfmn :
      abs (f m - f n) < δ :=
    hfClose m n hmFClose hnFClose

  have hgmn :
      abs (g m - g n) < δ :=
    hgClose m n hmGClose hnGClose

  have hFirst :
      abs (f m) *
          abs (g m - g n)
        <
      Bf * δ := by

    exact
      mul_lt_mul''
        hfm
        hgmn
        (abs_nonneg (f m))
        (abs_nonneg (g m - g n))

  have hSecond :
      abs (g n) *
          abs (f m - f n)
        <
      Bg * δ := by

    exact
      mul_lt_mul''
        hgn
        hfmn
        (abs_nonneg (g n))
        (abs_nonneg (f m - f n))

  have hSum :
      abs (f m) *
            abs (g m - g n) +
          abs (g n) *
            abs (f m - f n)
        <
      Bf * δ + Bg * δ :=
    add_lt_add hFirst hSecond

  calc
    abs
        (
          f m * g m -
            f n * g n
        )
        =
      abs
        (
          f m * (g m - g n) +
            g n * (f m - f n)
        ) := by
          congr 1
          ring

    _ ≤
      abs
          (
            f m *
              (g m - g n)
          ) +
        abs
          (
            g n *
              (f m - f n)
          ) :=
      abs_add_le _ _

    _ =
      abs (f m) *
            abs (g m - g n) +
        abs (g n) *
            abs (f m - f n) := by
      rw [abs_mul, abs_mul]

    _ <
      Bf * δ + Bg * δ :=
      hSum

    _ = ε := by
      dsimp [δ, D]
      field_simp [ne_of_gt hD]

/--
Pointwise products preserve asymptotic equivalence provided all four factors
are Cauchy tails.
-/
theorem DepthRealAsymptotic.mul
    {f f' g g' : Depth → ℝ}
    (hf : DepthRealCauchy f)
    (hf' : DepthRealCauchy f')
    (hg : DepthRealCauchy g)
    (hg' : DepthRealCauchy g')
    (hff' : DepthRealAsymptotic f f')
    (hgg' : DepthRealAsymptotic g g') :
    DepthRealAsymptotic
      (fun n => f n * g n)
      (fun n => f' n * g' n) := by

  intro ε hε

  obtain ⟨Bf, hBf, fBoundAnchor, hfBound⟩ :=
    hf.eventually_abs_lt

  obtain ⟨Bg', hBg', g'BoundAnchor, hg'Bound⟩ :=
    hg'.eventually_abs_lt

  let D : ℝ :=
    Bf + Bg'

  have hD :
      0 < D := by
    dsimp [D]
    nlinarith

  let δ : ℝ :=
    ε / D

  have hδ :
      0 < δ := by
    dsimp [δ]
    exact div_pos hε hD

  obtain ⟨fEqAnchor, hfEq⟩ :=
    hff' δ hδ

  obtain ⟨gEqAnchor, hgEq⟩ :=
    hgg' δ hδ

  let eqTail :=
    Depth.join fEqAnchor gEqAnchor

  let boundTail :=
    Depth.join fBoundAnchor g'BoundAnchor

  let anchor :=
    Depth.join boundTail eqTail

  refine ⟨anchor, ?_⟩
  intro n hn

  have hnBoundTail :
      Depth.AtOrAfter boundTail n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter boundTail eqTail)
      hn

  have hnEqTail :
      Depth.AtOrAfter eqTail n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter boundTail eqTail)
      hn

  have hnFBound :
      Depth.AtOrAfter fBoundAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        fBoundAnchor g'BoundAnchor)
      hnBoundTail

  have hnG'Bound :
      Depth.AtOrAfter g'BoundAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        fBoundAnchor g'BoundAnchor)
      hnBoundTail

  have hnFEq :
      Depth.AtOrAfter fEqAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        fEqAnchor gEqAnchor)
      hnEqTail

  have hnGEq :
      Depth.AtOrAfter gEqAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        fEqAnchor gEqAnchor)
      hnEqTail

  have hfn :
      abs (f n) < Bf :=
    hfBound n hnFBound

  have hg'n :
      abs (g' n) < Bg' :=
    hg'Bound n hnG'Bound

  have hfeq :
      abs (f n - f' n) < δ :=
    hfEq n hnFEq

  have hgeq :
      abs (g n - g' n) < δ :=
    hgEq n hnGEq

  have hFirst :
      abs (f n) *
          abs (g n - g' n)
        <
      Bf * δ := by

    exact
      mul_lt_mul''
        hfn
        hgeq
        (abs_nonneg (f n))
        (abs_nonneg (g n - g' n))

  have hSecond :
      abs (g' n) *
          abs (f n - f' n)
        <
      Bg' * δ := by

    exact
      mul_lt_mul''
        hg'n
        hfeq
        (abs_nonneg (g' n))
        (abs_nonneg (f n - f' n))

  have hSum :
      abs (f n) *
            abs (g n - g' n) +
          abs (g' n) *
            abs (f n - f' n)
        <
      Bf * δ + Bg' * δ :=
    add_lt_add hFirst hSecond

  calc
    abs
        (
          f n * g n -
            f' n * g' n
        )
        =
      abs
        (
          f n * (g n - g' n) +
            g' n * (f n - f' n)
        ) := by
          congr 1
          ring

    _ ≤
      abs
          (
            f n *
              (g n - g' n)
          ) +
        abs
          (
            g' n *
              (f n - f' n)
          ) :=
      abs_add_le _ _

    _ =
      abs (f n) *
            abs (g n - g' n) +
        abs (g' n) *
            abs (f n - f' n) := by
      rw [abs_mul, abs_mul]

    _ <
      Bf * δ + Bg' * δ :=
      hSum

    _ = ε := by
      dsimp [δ, D]
      field_simp [ne_of_gt hD]

/--
The logarithmic coordinate sequence of every intrinsic stream is a
`DepthRealCauchy` tail.
-/
theorem MulCauchyStream.logTerm_depthRealCauchy
    (s : PrimeTensor.MulCauchyStream) :
    DepthRealCauchy
      (
        fun n =>
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            s n
      ) := by

  exact
    PrimeTensor.Bridge.MulCauchyStream.logCauchy s

/--
Intrinsic asymptotic equivalence becomes bridge asymptotic equivalence of the
two log-coordinate sequences.
-/
theorem logTerm_depthRealAsymptotic
    {a b : PrimeTensor.MulCauchyStream}
    (h : PrimeTensor.MulAsymptotic a b) :
    DepthRealAsymptotic
      (
        fun n =>
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            a n
      )
      (
        fun n =>
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            b n
      ) := by

  exact
    logAsymptotic_of_mulAsymptotic h

/--
Ordinary logarithm of the conventional finite coupling target.
-/
noncomputable def finiteTargetLog
    (a b : PrimeTensor.MulRat) : ℝ :=
  Real.log
    (
      PrimeTensor.Bridge.finiteLogProductTarget
        a b
    )

/--
The semantic target is exactly multiplication in ordinary log coordinates.
-/
theorem finiteTargetLog_eq
    (a b : PrimeTensor.MulRat) :
    finiteTargetLog a b =
      Real.log
          (PrimeTensor.Bridge.MulRat.toReal a) *
        Real.log
          (PrimeTensor.Bridge.MulRat.toReal b) := by

  unfold
    finiteTargetLog
    PrimeTensor.Bridge.finiteLogProductTarget

  rw [Real.log_exp]

/--
Along two intrinsic Cauchy input streams, the logarithm of the exact finite
semantic coupling target is an ordinary Cauchy tail.
-/
theorem finiteTargetLog_depthRealCauchy
    (a b : PrimeTensor.MulCauchyStream) :
    DepthRealCauchy
      (
        fun n =>
          finiteTargetLog
            (a.term n)
            (b.term n)
      ) := by

  have ha :
      DepthRealCauchy
        (
          fun n =>
            PrimeTensor.Bridge.MulCauchyStream.logTerm
              a n
        ) :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy a

  have hb :
      DepthRealCauchy
        (
          fun n =>
            PrimeTensor.Bridge.MulCauchyStream.logTerm
              b n
        ) :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy b

  have hp :=
    ha.mul hb

  simpa only [
    finiteTargetLog_eq,
    PrimeTensor.Bridge.MulCauchyStream.logTerm
  ] using hp

/--
Replacing both intrinsic input streams by asymptotically equivalent
representatives changes the finite semantic target logarithm asymptotically by
zero.
-/
theorem finiteTargetLog_depthRealAsymptotic
    {a a' b b' : PrimeTensor.MulCauchyStream}
    (ha : PrimeTensor.MulAsymptotic a a')
    (hb : PrimeTensor.MulAsymptotic b b') :
    DepthRealAsymptotic
      (
        fun n =>
          finiteTargetLog
            (a.term n)
            (b.term n)
      )
      (
        fun n =>
          finiteTargetLog
            (a'.term n)
            (b'.term n)
      ) := by

  have hca :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy a

  have hca' :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy a'

  have hcb :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy b

  have hcb' :=
    PrimeTensor.Bridge.MulCauchyStream.logTerm_depthRealCauchy b'

  have haa' :=
    logTerm_depthRealAsymptotic ha

  have hbb' :=
    logTerm_depthRealAsymptotic hb

  have hp :=
    haa'.mul
      hca hca' hcb hcb' hbb'

  simpa only [
    finiteTargetLog_eq,
    PrimeTensor.Bridge.MulCauchyStream.logTerm
  ] using hp

end Bridge
end PrimeTensor
