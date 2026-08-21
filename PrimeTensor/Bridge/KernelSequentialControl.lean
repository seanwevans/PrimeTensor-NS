import PrimeTensor.Bridge.NormalizedTargetApprox
import PrimeTensor.Bridge.KernelSequentialReduction

/-!
# Concrete sequential control for the normalized kernel

The rate-normalized kernel already has a universal internal output rate.
The remaining completion obligation is therefore sequence-level continuity
with respect to its finite inputs.

This file proves that obligation in the conventional logarithmic bridge.

For a requested intrinsic radius `r`, work two successor levels finer.  Then

* normalized output -> its finite semantic target contributes `< r/4`;
* finite semantic target motion contributes `< r/4`;
* target -> normalized output contributes `< r/4`.

Hence the total logarithmic error is `< 3r/4 < r`, which translates back to
the intrinsic `ScaleWithin` relation.
-/

namespace PrimeTensor
namespace Bridge

/--
Three errors measured two successor levels finer still fit strictly inside the
original intrinsic logarithmic radius.
-/
theorem three_fine_logScaleRadii_lt
    (target : Depth) :
    logScaleRadius (.succ (.succ target)) +
        (
          logScaleRadius (.succ (.succ target)) +
            logScaleRadius (.succ (.succ target))
        )
      <
    logScaleRadius target := by

  simp only [logScaleRadius_succ]

  have hPos :=
    logScaleRadius_pos target

  linarith

namespace PrimePairApprox

/--
The rate-normalized concrete kernel has exactly the sequential input control
needed by diagonal completion.
-/
theorem rateNormalizedKernel_sequential_control :
    RateNormalizedKernelSequentialControlled := by

  unfold RateNormalizedKernelSequentialControlled

  refine
    {
      cauchy_input := ?_
      representative_input := ?_
    }

  · intro a b target

    let fine : Depth :=
      .succ (.succ target)

    have hFinePos :
        0 < logScaleRadius fine :=
      logScaleRadius_pos fine

    have hTargetCauchy :=
      finiteTargetLog_depthRealCauchy a b

    obtain ⟨targetAnchor, hTarget⟩ :=
      hTargetCauchy
        (logScaleRadius fine)
        hFinePos

    let stage : Depth :=
      .succ fine

    let anchor : Depth :=
      Depth.join stage targetAnchor

    refine ⟨anchor, ?_⟩

    intro m n hm hn

    have hnStage :
        Depth.AtOrAfter stage n :=
      Depth.atOrAfter_trans
        (Depth.left_atOrAfter stage targetAnchor)
        hn

    have hmTarget :
        Depth.AtOrAfter targetAnchor m :=
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter stage targetAnchor)
        hm

    have hnTarget :
        Depth.AtOrAfter targetAnchor n :=
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter stage targetAnchor)
        hn

    have hLeft :=
      rateNormalizedKernel_term_log_close_target
        (a.term m)
        (b.term m)
        fine
        n
        hnStage

    have hMiddle :=
      hTarget
        m n
        hmTarget hnTarget

    have hRight :=
      rateNormalizedKernel_term_log_close_target
        (a.term n)
        (b.term n)
        fine
        n
        hnStage

    apply
      (
        PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
          target
          (
            ((streamFiniteKernel.rateNormalized).realize
              (a.term m)
              (b.term m)).term n
          )
          (
            ((streamFiniteKernel.rateNormalized).realize
              (a.term n)
              (b.term n)).term n
          )
      ).2

    have hRightSymm :
        abs
            (
              finiteTargetLog
                  (a.term n)
                  (b.term n) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)).term n
                      )
                  )
            )
          <
        logScaleRadius fine := by

      rw [abs_sub_comm]

      exact hRight

    have hTail :
        abs
            (
              finiteTargetLog
                  (a.term m)
                  (b.term m) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)).term n
                      )
                  )
            )
          <
        logScaleRadius fine +
          logScaleRadius fine := by

      calc
        abs
            (
              finiteTargetLog
                  (a.term m)
                  (b.term m) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)).term n
                      )
                  )
            )
            ≤
          abs
              (
                finiteTargetLog
                    (a.term m)
                    (b.term m) -
                  finiteTargetLog
                    (a.term n)
                    (b.term n)
              ) +
            abs
              (
                finiteTargetLog
                    (a.term n)
                    (b.term n) -
                  Real.log
                    (
                      PrimeTensor.Bridge.MulRat.toReal
                        (
                          ((streamFiniteKernel.rateNormalized).realize
                            (a.term n)
                            (b.term n)).term n
                        )
                    )
              ) :=
          abs_sub_le _ _ _

        _ <
          logScaleRadius fine +
            logScaleRadius fine :=
          add_lt_add hMiddle hRightSymm

    calc
      abs
          (
            Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      ((streamFiniteKernel.rateNormalized).realize
                        (a.term m)
                        (b.term m)).term n
                    )
                ) -
              Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      ((streamFiniteKernel.rateNormalized).realize
                        (a.term n)
                        (b.term n)).term n
                    )
                )
          )
          ≤
        abs
            (
              Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term m)
                          (b.term m)).term n
                      )
                  ) -
                finiteTargetLog
                  (a.term m)
                  (b.term m)
            ) +
          abs
            (
              finiteTargetLog
                  (a.term m)
                  (b.term m) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)).term n
                      )
                  )
            ) :=
        abs_sub_le _ _ _

      _ <
        logScaleRadius fine +
          (
            logScaleRadius fine +
              logScaleRadius fine
          ) :=
        add_lt_add hLeft hTail

      _ =
        logScaleRadius (.succ (.succ target)) +
          (
            logScaleRadius (.succ (.succ target)) +
              logScaleRadius (.succ (.succ target))
          ) := by
        rfl

      _ <
        logScaleRadius target :=
        three_fine_logScaleRadii_lt target

  · intro a a' b b' ha hb target

    let fine : Depth :=
      .succ (.succ target)

    have hFinePos :
        0 < logScaleRadius fine :=
      logScaleRadius_pos fine

    have hTargetAsymptotic :=
      finiteTargetLog_depthRealAsymptotic
        ha hb

    obtain ⟨targetAnchor, hTarget⟩ :=
      hTargetAsymptotic
        (logScaleRadius fine)
        hFinePos

    let stage : Depth :=
      .succ fine

    let anchor : Depth :=
      Depth.join stage targetAnchor

    refine ⟨anchor, ?_⟩

    intro n hn

    have hnStage :
        Depth.AtOrAfter stage n :=
      Depth.atOrAfter_trans
        (Depth.left_atOrAfter stage targetAnchor)
        hn

    have hnTarget :
        Depth.AtOrAfter targetAnchor n :=
      Depth.atOrAfter_trans
        (Depth.right_atOrAfter stage targetAnchor)
        hn

    have hLeft :=
      rateNormalizedKernel_term_log_close_target
        (a.term n)
        (b.term n)
        fine
        n
        hnStage

    have hMiddle :=
      hTarget n hnTarget

    have hRight :=
      rateNormalizedKernel_term_log_close_target
        (a'.term n)
        (b'.term n)
        fine
        n
        hnStage

    apply
      (
        PrimeTensor.Bridge.MulRat.scaleWithin_iff_log
          target
          (
            ((streamFiniteKernel.rateNormalized).realize
              (a.term n)
              (b.term n)).term n
          )
          (
            ((streamFiniteKernel.rateNormalized).realize
              (a'.term n)
              (b'.term n)).term n
          )
      ).2

    have hRightSymm :
        abs
            (
              finiteTargetLog
                  (a'.term n)
                  (b'.term n) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a'.term n)
                          (b'.term n)).term n
                      )
                  )
            )
          <
        logScaleRadius fine := by

      rw [abs_sub_comm]

      exact hRight

    have hTail :
        abs
            (
              finiteTargetLog
                  (a.term n)
                  (b.term n) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a'.term n)
                          (b'.term n)).term n
                      )
                  )
            )
          <
        logScaleRadius fine +
          logScaleRadius fine := by

      calc
        abs
            (
              finiteTargetLog
                  (a.term n)
                  (b.term n) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a'.term n)
                          (b'.term n)).term n
                      )
                  )
            )
            ≤
          abs
              (
                finiteTargetLog
                    (a.term n)
                    (b.term n) -
                  finiteTargetLog
                    (a'.term n)
                    (b'.term n)
              ) +
            abs
              (
                finiteTargetLog
                    (a'.term n)
                    (b'.term n) -
                  Real.log
                    (
                      PrimeTensor.Bridge.MulRat.toReal
                        (
                          ((streamFiniteKernel.rateNormalized).realize
                            (a'.term n)
                            (b'.term n)).term n
                        )
                    )
              ) :=
          abs_sub_le _ _ _

        _ <
          logScaleRadius fine +
            logScaleRadius fine :=
          add_lt_add hMiddle hRightSymm

    calc
      abs
          (
            Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      ((streamFiniteKernel.rateNormalized).realize
                        (a.term n)
                        (b.term n)).term n
                    )
                ) -
              Real.log
                (
                  PrimeTensor.Bridge.MulRat.toReal
                    (
                      ((streamFiniteKernel.rateNormalized).realize
                        (a'.term n)
                        (b'.term n)).term n
                    )
                )
          )
          ≤
        abs
            (
              Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a.term n)
                          (b.term n)).term n
                      )
                  ) -
                finiteTargetLog
                  (a.term n)
                  (b.term n)
            ) +
          abs
            (
              finiteTargetLog
                  (a.term n)
                  (b.term n) -
                Real.log
                  (
                    PrimeTensor.Bridge.MulRat.toReal
                      (
                        ((streamFiniteKernel.rateNormalized).realize
                          (a'.term n)
                          (b'.term n)).term n
                      )
                  )
            ) :=
        abs_sub_le _ _ _

      _ <
        logScaleRadius fine +
          (
            logScaleRadius fine +
              logScaleRadius fine
          ) :=
        add_lt_add hLeft hTail

      _ =
        logScaleRadius (.succ (.succ target)) +
          (
            logScaleRadius (.succ (.succ target)) +
              logScaleRadius (.succ (.succ target))
          ) := by
        rfl

      _ <
        logScaleRadius target :=
        three_fine_logScaleRadii_lt target

/--
The normalized concrete kernel is completion-stable with no remaining
analytic hypothesis.
-/
theorem rateNormalizedKernel_completionStable :
    PrimeTensor.IsCouplingCompletionStable
      streamFiniteKernel.rateNormalized := by

  exact
    rateNormalizedKernel_completionStable_of_sequential
      rateNormalizedKernel_sequential_control

/--
The resulting normalized completed kernel is lawful.
-/
theorem normalizedCompletedKernel_final_lawful :
    PrimeTensor.IsMulCoupling
      (
        normalizedCompletedKernel
          rateNormalizedKernel_completionStable
      ) := by

  exact
    normalizedCompletedKernel_lawful
      rateNormalizedKernel_completionStable

/--
The final normalized completion agrees with the canonical finite coupling on
embedded finite multiplicative rationals.
-/
theorem normalizedCompletedKernel_final_agrees_finite
    (a b : PrimeTensor.MulRat) :
    (
      normalizedCompletedKernel
        rateNormalizedKernel_completionStable
    ).couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b := by

  exact
    normalizedCompletedKernel_agrees_finite
      rateNormalizedKernel_completionStable
      a b

end PrimePairApprox
end Bridge
end PrimeTensor
