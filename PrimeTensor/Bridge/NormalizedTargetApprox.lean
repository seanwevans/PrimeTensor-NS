import PrimeTensor.Bridge.LogProductContinuity
import PrimeTensor.Bridge.Convergence
import PrimeTensor.Fluid.CouplingNormalize

/-!
# Rate-normalized terms approximate their conventional targets

This is a bridge-only theorem layer.

A normalized stream need not preserve conventional convergence by a cofinal
reindexing argument: its chosen normalization schedule is not known to be
cofinal.  We therefore do not claim that.

Instead, for one requested intrinsic level, a normalized term sufficiently
deep in the *external* index is compared with one suitably late raw term.

* normalization puts the normalized term beyond the raw Cauchy anchor at a
  finer intrinsic level;
* ordinary convergence lets us choose another raw term beyond that same
  anchor whose logarithm is close to the conventional target;
* the native Cauchy estimate controls the two raw terms;
* the two finer log-radius errors fit strictly inside the requested radius.

This is exactly the finite-stage estimate needed by sequential completion.
-/

namespace PrimeTensor
namespace Bridge

namespace MulCauchyStream

/--
Conventional real convergence to a nonzero target implies convergence of the
ordinary logarithmic coordinates along the same native positive-depth tails.
-/
theorem convergesReal_logTail
    {s : PrimeTensor.MulCauchyStream}
    {x : ℝ}
    (hConv :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal s x)
    (hx : x ≠ 0) :
    ∀ ε : ℝ,
      0 < ε →
      ∃ anchor : Depth,
        ∀ n : Depth,
          Depth.AtOrAfter anchor n →
          abs
            (
              Real.log
                  (PrimeTensor.Bridge.MulCauchyStream.toRealTerm
                    s n) -
                Real.log x
            )
            < ε := by

  have hReal :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.toRealTerm s)
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds x) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.convergesReal_iff_tendsto
        s x
    ).mp hConv

  have hLog :=
    hReal.log hx

  rw [Metric.tendsto_nhds] at hLog

  intro ε hε

  have hEventually :=
    hLog ε hε

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

  exact hDist

/--
A rate-normalized term indexed at or after the successor of `level` has
logarithmic distance strictly below the radius for `level` from the
conventional limit of the original stream.

This does not require the normalization schedule itself to be cofinal.
-/
theorem normalize_log_close_limit
    (s : PrimeTensor.MulCauchyStream)
    {x : ℝ}
    (hConv :
      PrimeTensor.Bridge.MulCauchyStream.ConvergesReal s x)
    (hx : 0 < x)
    (level n : Depth)
    (hn :
      Depth.AtOrAfter (.succ level) n) :
    abs
      (
        Real.log
            (
              PrimeTensor.Bridge.MulRat.toReal
                (
                  (PrimeTensor.MulCauchyStream.normalize s).term n
                )
            ) -
          Real.log x
      )
      <
    PrimeTensor.Bridge.logScaleRadius level := by

  have hFinePos :
      0 <
        PrimeTensor.Bridge.logScaleRadius
          (.succ level) :=
    PrimeTensor.Bridge.logScaleRadius_pos
      (.succ level)

  obtain ⟨limitAnchor, hLimit⟩ :=
    PrimeTensor.Bridge.MulCauchyStream.convergesReal_logTail
      hConv
        (ne_of_gt hx)
        (PrimeTensor.Bridge.logScaleRadius
          (.succ level))
        hFinePos

  let k : Depth :=
    Depth.join
      (PrimeTensor.MulCauchyStream.scaleAnchor
        s (.succ level))
      limitAnchor

  have hkScale :
      Depth.AtOrAfter
        (PrimeTensor.MulCauchyStream.scaleAnchor
          s (.succ level))
        k := by
    dsimp [k]
    exact
      Depth.left_atOrAfter
        (PrimeTensor.MulCauchyStream.scaleAnchor
          s (.succ level))
        limitAnchor

  have hkLimit :
      Depth.AtOrAfter limitAnchor k := by
    dsimp [k]
    exact
      Depth.right_atOrAfter
        (PrimeTensor.MulCauchyStream.scaleAnchor
          s (.succ level))
        limitAnchor

  have hnNormAnchor :
      Depth.AtOrAfter
        (PrimeTensor.MulCauchyStream.scaleAnchor
          s (.succ level))
        (PrimeTensor.MulCauchyStream.normalizationStage
          s n) :=
    PrimeTensor.MulCauchyStream.scaleAnchor_atOrAfter_normalizationStage_of_atOrAfter
      s hn

  have hPairScale :
      PrimeTensor.MulRat.ScaleWithin
        (.succ level)
        (
          s.term
            (PrimeTensor.MulCauchyStream.normalizationStage
              s n)
        )
        (s.term k) :=
    PrimeTensor.MulCauchyStream.scaleAnchor_spec
      s (.succ level)
      (PrimeTensor.MulCauchyStream.normalizationStage
        s n)
      k
      hnNormAnchor
      hkScale

  have hPairLogRaw :
      abs
        (
          Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (
                    s.term
                      (PrimeTensor.MulCauchyStream.normalizationStage s n)
                  )
              ) -
            Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (s.term k)
              )
        )
        <
      PrimeTensor.Bridge.logScaleRadius
        (.succ level) :=
    (
      PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
        (.succ level)
        (
          s.term
            (PrimeTensor.MulCauchyStream.normalizationStage
              s n)
        )
        (s.term k)
    ).mp hPairScale

  have hPairLog :
      abs
        (
          Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (
                    (PrimeTensor.MulCauchyStream.normalize s).term n
                  )
              ) -
            Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (s.term k)
              )
        )
        <
      PrimeTensor.Bridge.logScaleRadius
        (.succ level) := by

    simpa only [
      PrimeTensor.MulCauchyStream.normalize_term
    ] using hPairLogRaw

  have hLimitLog :
      abs
        (
          Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (s.term k)
              ) -
            Real.log x
        )
        <
      PrimeTensor.Bridge.logScaleRadius
        (.succ level) := by

    simpa only [
      PrimeTensor.Bridge.MulCauchyStream.toRealTerm
    ] using hLimit k hkLimit

  calc
    abs
        (
          Real.log
              (
                PrimeTensor.Bridge.MulRat.toReal
                  (
                    (PrimeTensor.MulCauchyStream.normalize s).term n
                  )
              ) -
            Real.log x
        )
        ≤
      abs
          (
            Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      (PrimeTensor.MulCauchyStream.normalize s).term n
                    )
                ) -
              Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (s.term k)
                )
          ) +
        abs
          (
            Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (s.term k)
                ) -
              Real.log x
          ) :=
      abs_sub_le _ _ _

    _ <
      PrimeTensor.Bridge.logScaleRadius
            (.succ level) +
        PrimeTensor.Bridge.logScaleRadius
            (.succ level) :=
      add_lt_add hPairLog hLimitLog

    _ =
      PrimeTensor.Bridge.logScaleRadius level := by
      rw [
        PrimeTensor.Bridge.logScaleRadius_succ
      ]
      ring

end MulCauchyStream

namespace PrimePairApprox

/--
Concrete specialization: every sufficiently deep term of the rate-normalized
stream finite kernel is uniformly close, in log coordinates, to the exact
finite semantic target for its current finite inputs.

The depth threshold depends only on the requested intrinsic level, not on the
finite input pair.
-/
theorem rateNormalizedKernel_term_log_close_target
    (a b : PrimeTensor.MulRat)
    (level n : Depth)
    (hn :
      Depth.AtOrAfter (.succ level) n) :
    abs
      (
        Real.log
            (
              PrimeTensor.Bridge.MulRat.toReal
                (
                  (
                    (streamFiniteKernel.rateNormalized).realize a b
                  ).term n
                )
            ) -
          PrimeTensor.Bridge.finiteTargetLog a b
      )
      <
    PrimeTensor.Bridge.logScaleRadius level := by

  change
    abs
      (
        Real.log
            (
              PrimeTensor.Bridge.MulRat.toReal
                (
                  (
                    PrimeTensor.MulCauchyStream.normalize
                      (streamFiniteKernel.realize a b)
                  ).term n
                )
            ) -
          PrimeTensor.Bridge.finiteTargetLog a b
      )
      <
    PrimeTensor.Bridge.logScaleRadius level

  have h :=
    PrimeTensor.Bridge.MulCauchyStream.normalize_log_close_limit
      (streamFiniteKernel.realize a b)
        (
          streamFiniteKernel_convergesReal_finiteLogProduct
            a b
        )
        (
          PrimeTensor.Bridge.finiteLogProductTarget_pos
            a b
        )
        level n hn

  simpa only [
    PrimeTensor.Bridge.finiteTargetLog
  ] using h

end PrimePairApprox

end Bridge
end PrimeTensor
