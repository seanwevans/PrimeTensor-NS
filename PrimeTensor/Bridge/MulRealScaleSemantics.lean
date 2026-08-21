import PrimeTensor.Bridge.MulRealLogEmbedding
import PrimeTensor.Analysis.Derivative

/-!
# Intrinsic completed scale in logarithmic coordinates

For finite `MulRat`, `ScaleWithin level` is exactly the strict logarithmic
bound

    |log a - log b| < logScaleRadius level.

For completed `MulReal`, `ScaleNear` is defined by an eventual strict bound on
representative tails.  Passing to the completion can land on the boundary, so
the correct fixed-scale semantics are deliberately asymmetric:

    ScaleNear level x y
      -> |L x - L y| <= logScaleRadius level,

while

    |L x - L y| < logScaleRadius level
      -> ScaleNear level x y.

This is exactly enough to identify intrinsic convergence with ordinary
convergence of canonical logarithmic coordinates, because the native radii
become arbitrarily small.

As an immediate calculus consequence, perturbations approaching the
multiplicative pivot `1` are precisely perturbations whose logarithmic
coordinates tend to additive zero.
-/

namespace PrimeTensor
namespace Bridge

namespace MulReal

/--
Completed intrinsic nearness implies the corresponding closed logarithmic
radius bound.
-/
theorem scaleNear_logValue_le
    {level : Depth}
    {x y : PrimeTensor.MulReal}
    (hNear :
      PrimeTensor.MulReal.ScaleNear level x y) :
    abs
        (
          PrimeTensor.Bridge.MulReal.logValue x -
            PrimeTensor.Bridge.MulReal.logValue y
        )
      <=
    PrimeTensor.Bridge.logScaleRadius level := by

  obtain
    ⟨a, b, hax, hby, baseAnchor, hTail⟩ :=
    hNear

  rw [
    ← hax,
    ← hby,
    PrimeTensor.Bridge.MulReal.logValue_ofStream,
    PrimeTensor.Bridge.MulReal.logValue_ofStream
  ]

  by_contra hNot

  have hGap :
      PrimeTensor.Bridge.logScaleRadius level <
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          ) :=
    lt_of_not_ge hNot

  let ε : ℝ :=
    (
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          ) -
        PrimeTensor.Bridge.logScaleRadius level
    ) / 4

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨aAnchor, hA⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      a ε hε

  obtain ⟨bAnchor, hB⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      b ε hε

  let n : Depth :=
    Depth.join
      baseAnchor
      (Depth.join aAnchor bAnchor)

  have hnBase :
      Depth.AtOrAfter baseAnchor n := by
    dsimp [n]
    exact
      Depth.left_atOrAfter
        baseAnchor
        (Depth.join aAnchor bAnchor)

  have hnInner :
      Depth.AtOrAfter
        (Depth.join aAnchor bAnchor)
        n := by
    dsimp [n]
    exact
      Depth.right_atOrAfter
        baseAnchor
        (Depth.join aAnchor bAnchor)

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hnInner

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hnInner

  have hAFine :=
    hA n hnA

  have hBFine :=
    hB n hnB

  have hPairRaw :=
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
        level
        (a.term n)
        (b.term n)
    ).mp
      (hTail n hnBase)

  have hPair :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          )
        <
      PrimeTensor.Bridge.logScaleRadius level := by

    simpa only [
      PrimeTensor.Bridge.MulCauchyStream.logTerm
    ] using hPairRaw

  have hARev :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logTerm a n
          )
        <
      ε := by

    rw [abs_sub_comm]

    exact hAFine

  have hFirst :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          )
        <
      ε +
        PrimeTensor.Bridge.logScaleRadius level := by

    calc
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          )
          <=
        abs
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a -
                PrimeTensor.Bridge.MulCauchyStream.logTerm a n
            ) +
          abs
            (
              PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
                PrimeTensor.Bridge.MulCauchyStream.logTerm b n
            ) :=
        abs_sub_le _ _ _

      _ <
        ε +
          PrimeTensor.Bridge.logScaleRadius level :=
        add_lt_add hARev hPair

  have hTotal :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          )
        <
      (
        ε +
          PrimeTensor.Bridge.logScaleRadius level
      ) + ε := by

    calc
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          )
          <=
        abs
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a -
                PrimeTensor.Bridge.MulCauchyStream.logTerm b n
            ) +
          abs
            (
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n -
                PrimeTensor.Bridge.MulCauchyStream.logLimit b
            ) :=
        abs_sub_le _ _ _

      _ <
        (
          ε +
            PrimeTensor.Bridge.logScaleRadius level
        ) + ε :=
        add_lt_add hFirst hBFine

  have hImpossible :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          )
        <
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          ) := by

    calc
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          )
          <
        (
          ε +
            PrimeTensor.Bridge.logScaleRadius level
        ) + ε :=
        hTotal

      _ <
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          ) := by
        dsimp [ε]
        linarith

  exact
    (lt_irrefl _ hImpossible)

/--
A strict logarithmic radius bound produces completed intrinsic nearness at the
same native scale.
-/
theorem scaleNear_of_logValue_lt
    {level : Depth}
    {x y : PrimeTensor.MulReal}
    (hLog :
      abs
          (
            PrimeTensor.Bridge.MulReal.logValue x -
              PrimeTensor.Bridge.MulReal.logValue y
          )
        <
      PrimeTensor.Bridge.logScaleRadius level) :
    PrimeTensor.MulReal.ScaleNear level x y := by

  refine Quotient.inductionOn₂ x y ?_ hLog

  intro a b hLogRep

  change
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a -
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        )
      <
    PrimeTensor.Bridge.logScaleRadius level
    at hLogRep

  let gap : ℝ :=
    PrimeTensor.Bridge.logScaleRadius level -
      abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a -
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        )

  have hGap :
      0 < gap := by
    dsimp [gap]
    linarith

  let ε : ℝ :=
    gap / 4

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨aAnchor, hA⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      a ε hε

  obtain ⟨bAnchor, hB⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
      b ε hε

  let anchor : Depth :=
    Depth.join aAnchor bAnchor

  refine
    ⟨a, b, rfl, rfl, anchor, ?_⟩

  intro n hn

  have hnA :
      Depth.AtOrAfter aAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter aAnchor bAnchor)
      hn

  have hnB :
      Depth.AtOrAfter bAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter aAnchor bAnchor)
      hn

  have hAFine :=
    hA n hnA

  have hBFine :=
    hB n hnB

  apply
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
        level
        (a.term n)
        (b.term n)
    ).2

  change
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n
        )
      <
    PrimeTensor.Bridge.logScaleRadius level

  have hBRev :
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit b -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          )
        <
      ε := by

    rw [abs_sub_comm]

    exact hBFine

  calc
    abs
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
            PrimeTensor.Bridge.MulCauchyStream.logTerm b n
        )
        <=
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
          ) +
        abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a -
              PrimeTensor.Bridge.MulCauchyStream.logTerm b n
          ) :=
      abs_sub_le _ _ _

    _ <=
      abs
          (
            PrimeTensor.Bridge.MulCauchyStream.logTerm a n -
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
          ) +
        (
          abs
              (
                PrimeTensor.Bridge.MulCauchyStream.logLimit a -
                  PrimeTensor.Bridge.MulCauchyStream.logLimit b
              ) +
            abs
              (
                PrimeTensor.Bridge.MulCauchyStream.logLimit b -
                  PrimeTensor.Bridge.MulCauchyStream.logTerm b n
              )
        ) := by
      apply add_le_add_right
      exact abs_sub_le _ _ _

    _ <
      ε +
        (
          abs
              (
                PrimeTensor.Bridge.MulCauchyStream.logLimit a -
                  PrimeTensor.Bridge.MulCauchyStream.logLimit b
              ) +
            ε
        ) :=
      add_lt_add hAFine
        (add_lt_add_right hBRev _)

    _ <
      PrimeTensor.Bridge.logScaleRadius level := by
      dsimp [ε, gap]
      linarith

/--
Intrinsic convergence on the completed multiplicative carrier is exactly
ordinary real convergence of canonical logarithmic coordinates.
-/
theorem convergesTo_iff_logValue_tendsto
    (s : PrimeTensor.MulReal.Seq)
    (x : PrimeTensor.MulReal) :
    PrimeTensor.MulReal.ConvergesTo s x ↔
      Filter.Tendsto
        (
          fun n : Depth =>
            PrimeTensor.Bridge.MulReal.logValue (s n)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulReal.logValue x
            )
        ) := by

  constructor

  · intro hConv

    rw [Metric.tendsto_nhds]

    intro ε hε

    obtain ⟨level, hRadius⟩ :=
      PrimeTensor.Bridge.exists_logScaleRadius_lt hε

    obtain ⟨anchor, hTail⟩ :=
      hConv level

    rw [
      PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
    ]

    refine ⟨anchor, ?_⟩

    intro n hn

    rw [Real.dist_eq]

    exact
      lt_of_le_of_lt
        (
          PrimeTensor.Bridge.MulReal.scaleNear_logValue_le
            (hTail n hn)
        )
        hRadius

  · intro hConv
    intro level

    have hRadiusPos :
        0 <
          PrimeTensor.Bridge.logScaleRadius level :=
      PrimeTensor.Bridge.logScaleRadius_pos level

    rw [Metric.tendsto_nhds] at hConv

    have hEventually :=
      hConv
        (PrimeTensor.Bridge.logScaleRadius level)
        hRadiusPos

    rw [
      PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
    ] at hEventually

    obtain ⟨anchor, hTail⟩ :=
      hEventually

    refine ⟨anchor, ?_⟩

    intro n hn

    have hDist :=
      hTail n hn

    rw [Real.dist_eq] at hDist

    exact
      PrimeTensor.Bridge.MulReal.scaleNear_of_logValue_lt
        hDist

end MulReal

namespace MulDifferential

/--
A perturbation approaches the multiplicative pivot exactly when its canonical
logarithmic coordinate tends to additive zero.
-/
theorem approachesPivot_iff_logValue_tendsto_zero
    (h : PrimeTensor.MulReal.Seq) :
    PrimeTensor.MulDifferential.ApproachesPivot h ↔
      Filter.Tendsto
        (
          fun n : Depth =>
            PrimeTensor.Bridge.MulReal.logValue (h n)
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds 0) := by

  unfold PrimeTensor.MulDifferential.ApproachesPivot

  rw [
    PrimeTensor.Bridge.MulReal.convergesTo_iff_logValue_tendsto,
    PrimeTensor.Bridge.MulReal.logValue_one
  ]

end MulDifferential

end Bridge
end PrimeTensor
