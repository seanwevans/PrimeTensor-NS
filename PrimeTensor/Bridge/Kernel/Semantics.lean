import PrimeTensor.Bridge.MulReal.Log
import PrimeTensor.Bridge.Kernel.Final
import PrimeTensor.Bridge.NormalizedTarget.Approx

/-!
# Semantics of the completed logarithmic product coupling

The completed coupling was constructed intrinsically by diagonal completion of
the rate-normalized finite kernel.  `MulRealLog` supplies a canonical
conventional logarithmic coordinate on every completed `MulReal`.

This file proves the semantic identity on arbitrary completed inputs:

    logValue (logProductCoupling.couple a b)
      = logValue a * logValue b.

The proof does not appeal to density of finite rationals.  Instead it follows
the actual completion construction:

1. representative input streams have logarithmic limits `A` and `B`;
2. the finite semantic target at native depth `n` is exactly the product of
   the two input logarithms at `n`, hence tends to `A * B`;
3. each rate-normalized diagonal term is asymptotic, in logarithmic
   coordinates, to that finite target;
4. uniqueness of logarithmic limits identifies the completed output limit with
   `A * B`;
5. quotient induction descends the statement to arbitrary `MulReal` inputs.
-/

namespace PrimeTensor
namespace Bridge

namespace MulCauchyStream

/--
Whole-tail logarithmic convergence is exactly filter convergence along the
native positive-depth tail filter.
-/
theorem logConverges_iff_tendsto
    (s : PrimeTensor.MulCauchyStream)
    (x : ℝ) :
    PrimeTensor.Bridge.MulCauchyStream.LogConverges s x ↔
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm s)
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds x) := by

  rw [Metric.tendsto_nhds]

  constructor

  · intro h ε hε

    rw [
      PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
    ]

    obtain ⟨anchor, hTail⟩ :=
      h ε hε

    refine ⟨anchor, ?_⟩

    intro n hn

    rw [Real.dist_eq]

    exact hTail n hn

  · intro h ε hε

    have hEventually :=
      h ε hε

    rw [
      PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
    ] at hEventually

    obtain ⟨anchor, hTail⟩ :=
      hEventually

    refine ⟨anchor, ?_⟩

    intro n hn

    have hNear :=
      hTail n hn

    rw [Real.dist_eq] at hNear

    exact hNear

end MulCauchyStream

/--
If two real-valued native-depth functions are asymptotic and the second tends
to `x`, then the first tends to `x`.
-/
theorem DepthRealAsymptotic.tendsto_of_tendsto
    {f g : Depth → ℝ}
    {x : ℝ}
    (hfg : DepthRealAsymptotic f g)
    (hg :
      Filter.Tendsto
        g
        PrimeTensor.Bridge.Depth.tailFilter
        (nhds x)) :
    Filter.Tendsto
      f
      PrimeTensor.Bridge.Depth.tailFilter
      (nhds x) := by

  rw [Metric.tendsto_nhds] at hg ⊢

  intro ε hε

  have hHalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨fgAnchor, hFG⟩ :=
    hfg (ε / 2) hHalf

  have hGEventually :=
    hg (ε / 2) hHalf

  rw [
    PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
  ] at hGEventually

  obtain ⟨gAnchor, hG⟩ :=
    hGEventually

  rw [
    PrimeTensor.Bridge.Depth.eventually_tailFilter_iff
  ]

  let anchor : Depth :=
    Depth.join fgAnchor gAnchor

  refine ⟨anchor, ?_⟩

  intro n hn

  have hnFG :
      Depth.AtOrAfter fgAnchor n :=
    Depth.atOrAfter_trans
      (Depth.left_atOrAfter fgAnchor gAnchor)
      hn

  have hnG :
      Depth.AtOrAfter gAnchor n :=
    Depth.atOrAfter_trans
      (Depth.right_atOrAfter fgAnchor gAnchor)
      hn

  have hNearFG :=
    hFG n hnFG

  have hNearG :=
    hG n hnG

  rw [Real.dist_eq] at hNearG ⊢

  calc
    abs (f n - x)
        ≤
      abs (f n - g n) +
        abs (g n - x) :=
      abs_sub_le _ _ _

    _ <
      ε / 2 + ε / 2 :=
      add_lt_add hNearFG hNearG

    _ = ε := by
      ring

namespace PrimePairApprox

/--
Along two representative input streams, the exact finite semantic target tends
to the product of their canonical logarithmic limits.
-/
theorem finiteTargetLog_tendsto_logLimits
    (a b : PrimeTensor.MulCauchyStream) :
    Filter.Tendsto
      (fun n : Depth =>
        finiteTargetLog
          (a.term n)
          (b.term n))
      PrimeTensor.Bridge.Depth.tailFilter
      (
        nhds
          (
            PrimeTensor.Bridge.MulCauchyStream.logLimit a *
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
          )
      ) := by

  have ha :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm a)
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a
            )
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        a
        (PrimeTensor.Bridge.MulCauchyStream.logLimit a)
    ).mp
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          a
      )

  have hb :
      Filter.Tendsto
        (PrimeTensor.Bridge.MulCauchyStream.logTerm b)
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit b
            )
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        b
        (PrimeTensor.Bridge.MulCauchyStream.logLimit b)
    ).mp
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          b
      )

  have hMul :=
    ha.mul hb

  simpa only [
    finiteTargetLog_eq,
    PrimeTensor.Bridge.MulCauchyStream.logTerm
  ] using hMul

/--
The logarithmic coordinates of the normalized diagonal are asymptotic to the
exact finite semantic targets at the same native depth.
-/
theorem rateNormalizedKernel_diagonal_log_asymptotic_target
    (a b : PrimeTensor.MulCauchyStream) :
    DepthRealAsymptotic
      (
        fun n : Depth =>
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            (
              (streamFiniteKernel.rateNormalized).diagonal
                rateNormalizedKernel_completionStable.diagonal_cauchy
                a b
            )
            n
      )
      (
        fun n : Depth =>
          finiteTargetLog
            (a.term n)
            (b.term n)
      ) := by

  intro ε hε

  obtain ⟨level, hLevel⟩ :=
    exists_logScaleRadius_lt hε

  refine ⟨.succ level, ?_⟩

  intro n hn

  have hNear :=
    rateNormalizedKernel_term_log_close_target
      (a.term n)
      (b.term n)
      level
      n
      hn

  have hNear' :
      abs
          (
            Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      (
                        (streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)
                      ).term n
                    )
                ) -
              finiteTargetLog
                (a.term n)
                (b.term n)
          )
        <
      ε :=
    lt_trans hNear hLevel

  simpa only [
    PrimeTensor.Bridge.MulCauchyStream.logTerm,
    PrimeTensor.StreamFiniteMulCoupling.diagonal_term
  ] using hNear'

/--
The normalized completed diagonal has logarithmic limit equal to the product
of the logarithmic limits of its two representative input streams.
-/
theorem rateNormalizedKernel_diagonal_logLimit
    (a b : PrimeTensor.MulCauchyStream) :
    PrimeTensor.Bridge.MulCauchyStream.logLimit
        (
          (streamFiniteKernel.rateNormalized).diagonal
            rateNormalizedKernel_completionStable.diagonal_cauchy
            a b
        )
      =
    PrimeTensor.Bridge.MulCauchyStream.logLimit a *
      PrimeTensor.Bridge.MulCauchyStream.logLimit b := by

  let out : PrimeTensor.MulCauchyStream :=
    (streamFiniteKernel.rateNormalized).diagonal
      rateNormalizedKernel_completionStable.diagonal_cauchy
      a b

  have hTarget :=
    finiteTargetLog_tendsto_logLimits a b

  have hAsymptotic :
      DepthRealAsymptotic
        (
          fun n : Depth =>
            PrimeTensor.Bridge.MulCauchyStream.logTerm
              out n
        )
        (
          fun n : Depth =>
            finiteTargetLog
              (a.term n)
              (b.term n)
        ) := by

    dsimp [out]

    exact
      rateNormalizedKernel_diagonal_log_asymptotic_target
        a b

  have hOutTendsto :
      Filter.Tendsto
        (
          PrimeTensor.Bridge.MulCauchyStream.logTerm
            out
        )
        PrimeTensor.Bridge.Depth.tailFilter
        (
          nhds
            (
              PrimeTensor.Bridge.MulCauchyStream.logLimit a *
                PrimeTensor.Bridge.MulCauchyStream.logLimit b
            )
        ) :=
    hAsymptotic.tendsto_of_tendsto hTarget

  have hOutConverges :
      PrimeTensor.Bridge.MulCauchyStream.LogConverges
        out
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a *
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        ) :=
    (
      PrimeTensor.Bridge.MulCauchyStream.logConverges_iff_tendsto
        out
        (
          PrimeTensor.Bridge.MulCauchyStream.logLimit a *
            PrimeTensor.Bridge.MulCauchyStream.logLimit b
        )
    ).mpr hOutTendsto

  exact
    PrimeTensor.Bridge.MulCauchyStream.logConverges_unique
      (
        PrimeTensor.Bridge.MulCauchyStream.logConverges_logLimit
          out
      )
      hOutConverges

/--
Full completed semantics of the canonical coupling.

This is the arbitrary-`MulReal` extension of the finite identity

    log C_e(a,b) = log a * log b.
-/
theorem logProductCoupling_logValue
    (a b : PrimeTensor.MulReal) :
    PrimeTensor.Bridge.MulReal.logValue
        (
          logProductCoupling.couple a b
        )
      =
    PrimeTensor.Bridge.MulReal.logValue a *
      PrimeTensor.Bridge.MulReal.logValue b := by

  refine Quotient.inductionOn₂ a b ?_

  intro sa sb

  change
    PrimeTensor.Bridge.MulReal.logValue
        (
          PrimeTensor.MulReal.ofStream
            (
              (streamFiniteKernel.rateNormalized).diagonal
                rateNormalizedKernel_completionStable.diagonal_cauchy
                sa sb
            )
        )
      =
    PrimeTensor.Bridge.MulReal.logValue
        (PrimeTensor.MulReal.ofStream sa) *
      PrimeTensor.Bridge.MulReal.logValue
        (PrimeTensor.MulReal.ofStream sb)

  rw [
    PrimeTensor.Bridge.MulReal.logValue_ofStream,
    PrimeTensor.Bridge.MulReal.logValue_ofStream,
    PrimeTensor.Bridge.MulReal.logValue_ofStream
  ]

  exact
    rateNormalizedKernel_diagonal_logLimit
      sa sb

end PrimePairApprox
end Bridge
end PrimeTensor
