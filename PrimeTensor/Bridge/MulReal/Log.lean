import PrimeTensor.Bridge.Log.Cauchy
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Canonical logarithmic value of completed multiplicative reals

This file is bridge-only.

Every intrinsic `MulCauchyStream` is already known to be Cauchy in ordinary
real logarithmic coordinates.  We now use the canonical natural cofinal
subsequence

    depthFromNat 0, depthFromNat 1, ...

to obtain a real limit from completeness of `ℝ`, then prove the entire native
`Depth` tail converges to that same limit.

Intrinsic asymptotic equivalence forces equal logarithmic limits, so the limit
descends through the quotient and gives a conventional logarithmic coordinate

    MulReal.logValue : MulReal → ℝ.

No additive structure is introduced into the intrinsic carrier.
-/

namespace PrimeTensor
namespace Bridge

/-- Conventional zero-based index of a native positive depth. -/
def depthIndex : Depth → ℕ
  | .one => 0
  | .succ d => depthIndex d + 1

@[simp]
theorem depthIndex_one :
    depthIndex .one = 0 := by
  rfl

@[simp]
theorem depthIndex_succ
    (d : Depth) :
    depthIndex (.succ d) =
      depthIndex d + 1 := by
  rfl

/-- `depthFromNat` and `depthIndex` are inverse in the native direction. -/
@[simp]
theorem depthFromNat_depthIndex :
    ∀ d : Depth,
      depthFromNat (depthIndex d) = d

  | .one => by
      rfl

  | .succ d => by
      rw [
        depthIndex_succ,
        depthFromNat_succ,
        depthFromNat_depthIndex d
      ]

/--
Advancing the natural index advances along the native `AtOrAfter` relation.
-/
theorem depthFromNat_atOrAfter_add
    (n k : ℕ) :
    Depth.AtOrAfter
      (depthFromNat n)
      (depthFromNat (n + k)) := by

  induction k with
  | zero =>
      simp only [Nat.add_zero]
      exact Depth.AtOrAfter.here _

  | succ k ih =>
      rw [
        Nat.add_succ,
        depthFromNat_succ
      ]
      exact Depth.AtOrAfter.later ih

/--
Every native depth anchor is reached by the canonical natural subsequence, and
all later natural offsets remain in its tail.
-/
theorem depth_atOrAfter_depthFromNat_offset
    (d : Depth)
    (k : ℕ) :
    Depth.AtOrAfter
      d
      (depthFromNat (depthIndex d + k)) := by

  simpa only [depthFromNat_depthIndex] using
    depthFromNat_atOrAfter_add
      (depthIndex d) k

namespace MulCauchyStream

/-- Natural cofinal subsequence of the logarithmic coordinates. -/
noncomputable def natLogTerm
    (s : PrimeTensor.MulCauchyStream)
    (n : ℕ) : ℝ :=
  PrimeTensor.Bridge.MulCauchyStream.logTerm
    s
    (depthFromNat n)

/--
The canonical natural logarithmic subsequence is an ordinary metric Cauchy
sequence.
-/
theorem natLogTerm_cauchy
    (s : PrimeTensor.MulCauchyStream) :
    CauchySeq (natLogTerm s) := by

  rw [Metric.cauchySeq_iff]

  intro ε hε

  obtain ⟨anchor, hTail⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logCauchy s
      ε hε

  let N : ℕ :=
    depthIndex anchor

  refine ⟨N, ?_⟩

  intro m hm n hn

  obtain ⟨km, hkm⟩ :=
    Nat.exists_eq_add_of_le hm

  obtain ⟨kn, hkn⟩ :=
    Nat.exists_eq_add_of_le hn

  have hmTail :
      Depth.AtOrAfter
        anchor
        (depthFromNat m) := by

    subst m

    exact
      depth_atOrAfter_depthFromNat_offset
        anchor km

  have hnTail :
      Depth.AtOrAfter
        anchor
        (depthFromNat n) := by

    subst n

    exact
      depth_atOrAfter_depthFromNat_offset
        anchor kn

  rw [Real.dist_eq]

  exact hTail
    (depthFromNat m)
    (depthFromNat n)
    hmTail hnTail

/--
Every intrinsic Cauchy stream has a conventional real logarithmic limit along
the canonical natural subsequence.
-/
theorem exists_natLogLimit
    (s : PrimeTensor.MulCauchyStream) :
    ∃ x : ℝ,
      Filter.Tendsto
        (natLogTerm s)
        Filter.atTop
        (nhds x) := by

  exact
    cauchySeq_tendsto_of_complete
      (natLogTerm_cauchy s)

/--
Ordinary epsilon convergence of the whole native `Depth` tail in logarithmic
coordinates.
-/
def LogConverges
    (s : PrimeTensor.MulCauchyStream)
    (x : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ anchor : Depth,
      ∀ n : Depth,
        Depth.AtOrAfter anchor n →
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm s n -
              x
          )
          < ε

/--
A limit of the natural cofinal subsequence is also the limit of the entire
native positive-depth tail.
-/
theorem logConverges_of_natLogTerm_tendsto
    {s : PrimeTensor.MulCauchyStream}
    {x : ℝ}
    (hNat :
      Filter.Tendsto
        (natLogTerm s)
        Filter.atTop
        (nhds x)) :
    LogConverges s x := by

  intro ε hε

  have hHalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨cauchyAnchor, hCauchy⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logCauchy s
      (ε / 2) hHalf

  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hNat)
      (ε / 2) hHalf

  let K : ℕ :=
    depthIndex cauchyAnchor + N

  let witness : Depth :=
    depthFromNat K

  have hwCauchy :
      Depth.AtOrAfter cauchyAnchor witness := by

    dsimp [witness, K]

    exact
      depth_atOrAfter_depthFromNat_offset
        cauchyAnchor N

  have hNK :
      N ≤ K := by

    dsimp [K]

    exact Nat.le_add_left N (depthIndex cauchyAnchor)

  have hwLimitDist :
      dist
        (natLogTerm s K)
        x
        <
      ε / 2 :=
    hN K hNK

  have hwLimit :
      abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm
              s witness -
            x
        )
        <
      ε / 2 := by

    rw [Real.dist_eq] at hwLimitDist

    simpa only [
      natLogTerm,
      witness
    ] using hwLimitDist

  let anchor : Depth :=
    Depth.join cauchyAnchor witness

  refine ⟨anchor, ?_⟩

  intro n hn

  have hnCauchy :
      Depth.AtOrAfter cauchyAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        cauchyAnchor witness)
      hn

  have hNear :
      abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm s n -
            PrimeTensor.Bridge.MulCauchyStream.logTerm
              s witness
        )
        <
      ε / 2 :=
    hCauchy
      n witness
      hnCauchy hwCauchy

  calc
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm s n -
            x
        )
        ≤
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm s n -
              PrimeTensor.Bridge.MulCauchyStream.logTerm
                s witness
          ) +
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm
                s witness -
              x
          ) :=
      abs_sub_le _ _ _

    _ <
      ε / 2 + ε / 2 :=
      add_lt_add hNear hwLimit

    _ = ε := by
      ring

/-- Every intrinsic Cauchy stream has a whole-tail logarithmic limit. -/
theorem exists_logLimit
    (s : PrimeTensor.MulCauchyStream) :
    ∃ x : ℝ,
      LogConverges s x := by

  obtain ⟨x, hx⟩ :=
    exists_natLogLimit s

  exact
    ⟨x,
      logConverges_of_natLogTerm_tendsto hx⟩

/-- Whole-tail logarithmic limits are unique. -/
theorem logConverges_unique
    {s : PrimeTensor.MulCauchyStream}
    {x y : ℝ}
    (hx : LogConverges s x)
    (hy : LogConverges s y) :
    x = y := by

  by_contra hxy

  have hDistPos :
      0 < abs (x - y) := by
    apply abs_pos.mpr
    exact sub_ne_zero.mpr hxy

  let ε : ℝ :=
    abs (x - y) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨ax, hax⟩ :=
    hx ε hε

  obtain ⟨ay, hay⟩ :=
    hy ε hε

  let n : Depth :=
    Depth.join ax ay

  have hnx :
      Depth.AtOrAfter ax n := by
    dsimp [n]
    exact Depth.left_atOrAfter ax ay

  have hny :
      Depth.AtOrAfter ay n := by
    dsimp [n]
    exact Depth.right_atOrAfter ax ay

  have hxNear :=
    hax n hnx

  have hyNearRaw :=
    hay n hny

  have hyNear :
      abs
        (
          y -
            PrimeTensor.Bridge.MulCauchyStream.logTerm s n
        )
        <
      ε := by

    rw [abs_sub_comm]

    exact hyNearRaw

  have hContr :
      abs (x - y) <
        abs (x - y) := by

    calc
      abs (x - y)
          ≤
        abs
            (
              x -
                PrimeTensor.Bridge.MulCauchyStream.logTerm s n
            ) +
          abs
            (
              PrimeTensor.Bridge.MulCauchyStream.logTerm s n -
                y
            ) :=
        abs_sub_le _ _ _

      _ <
        ε + ε := by
        apply add_lt_add

        · rw [abs_sub_comm]
          exact hxNear

        · exact hyNearRaw

      _ <
        abs (x - y) := by
        dsimp [ε]
        linarith

  exact (lt_irrefl _ hContr)

/--
Asymptotically equivalent representatives share every logarithmic limit.
-/
theorem logConverges_of_asymptotic
    {a b : PrimeTensor.MulCauchyStream}
    {x : ℝ}
    (ha : LogConverges a x)
    (hab : PrimeTensor.MulAsymptotic a b) :
    LogConverges b x := by

  intro ε hε

  have hHalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨aAnchor, haTail⟩ :=
    ha (ε / 2) hHalf

  obtain ⟨abAnchor, habTail⟩ :=
    (PrimeTensor.Bridge.logAsymptotic_of_mulAsymptotic hab)
      (ε / 2) hHalf

  let anchor : Depth :=
    Depth.join aAnchor abAnchor

  refine ⟨anchor, ?_⟩

  intro n hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter
        aAnchor abAnchor)
      hn

  have hnAB :
      Depth.AtOrAfter abAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter
        aAnchor abAnchor)
      hn

  have hA :=
    haTail n hnA

  have hAB :=
    habTail n hnAB

  have hABSymm :
      abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm b n -
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n
        )
        <
      ε / 2 := by

    rw [abs_sub_comm]

    exact hAB

  calc
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm b n -
            x
        )
        ≤
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n -
              PrimeTensor.Bridge.MulCauchyStream.logTerm a n
          ) +
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              x
          ) :=
      abs_sub_le _ _ _

    _ <
      ε / 2 + ε / 2 :=
      add_lt_add hABSymm hA

    _ = ε := by
      ring

/-- Chosen canonical logarithmic limit of one stream representative. -/
noncomputable def logLimit
    (s : PrimeTensor.MulCauchyStream) : ℝ :=
  Classical.choose (exists_logLimit s)

/-- The chosen logarithmic limit actually is the stream limit. -/
theorem logConverges_logLimit
    (s : PrimeTensor.MulCauchyStream) :
    LogConverges s (logLimit s) :=
  Classical.choose_spec (exists_logLimit s)

/--
Intrinsic asymptotic equivalence forces equality of the chosen logarithmic
limits.
-/
theorem logLimit_eq_of_asymptotic
    {a b : PrimeTensor.MulCauchyStream}
    (hab : PrimeTensor.MulAsymptotic a b) :
    logLimit a = logLimit b := by

  exact
    logConverges_unique
      (
        logConverges_of_asymptotic
          (logConverges_logLimit a)
          hab
      )
      (logConverges_logLimit b)

end MulCauchyStream

namespace MulReal

/--
Canonical conventional logarithmic coordinate of a completed multiplicative
real.
-/
noncomputable def logValue
    (x : PrimeTensor.MulReal) : ℝ :=
  Quotient.lift
    PrimeTensor.Bridge.MulCauchyStream.logLimit
    (by
      intro a b hab
      exact
        PrimeTensor.Bridge.MulCauchyStream.logLimit_eq_of_asymptotic
          hab)
    x

@[simp]
theorem logValue_ofStream
    (s : PrimeTensor.MulCauchyStream) :
    logValue (PrimeTensor.MulReal.ofStream s) =
      PrimeTensor.Bridge.MulCauchyStream.logLimit s := by
  rfl

end MulReal

end Bridge
end PrimeTensor
