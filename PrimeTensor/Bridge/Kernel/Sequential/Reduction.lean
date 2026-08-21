import PrimeTensor.Bridge.Kernel.Normalized.Completion
import PrimeTensor.Fluid.Coupling.Sequential.Control

/-!
# Sequential-control reduction for the normalized concrete kernel

The earlier tail-input criterion is stronger than necessary because it
quantifies over arbitrary nearby finite rationals.

For completion we only need sequence-level continuity of the rate-normalized
kernel along:

* actual Cauchy input tails;
* asymptotically equivalent representative tails.

This file makes that the concrete remaining analytic hypothesis.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
Sequence-level continuity is the remaining concrete analytic obligation for the
rate-normalized kernel.
-/
def RateNormalizedKernelSequentialControlled : Prop :=
  PrimeTensor.CouplingSequentialScaleControl
    streamFiniteKernel.rateNormalized

/--
Sequential control suffices for completion stability of the normalized concrete
kernel.
-/
theorem rateNormalizedKernel_completionStable_of_sequential
    (hSeq : RateNormalizedKernelSequentialControlled) :
    PrimeTensor.IsCouplingCompletionStable
      streamFiniteKernel.rateNormalized := by

  exact
    streamFiniteKernel.rateNormalized_completionStable_of_sequentialControl
      hSeq

/--
Construct the completed concrete coupling from sequential control alone.
-/
noncomputable def normalizedCompletedKernel_of_sequential
    (hSeq : RateNormalizedKernelSequentialControlled) :
    PrimeTensor.MulCoupling :=
  normalizedCompletedKernel
    (rateNormalizedKernel_completionStable_of_sequential
      hSeq)

/--
The sequentially-controlled normalized completion is lawful.
-/
theorem normalizedCompletedKernel_of_sequential_lawful
    (hSeq : RateNormalizedKernelSequentialControlled) :
    PrimeTensor.IsMulCoupling
      (normalizedCompletedKernel_of_sequential hSeq) := by

  unfold normalizedCompletedKernel_of_sequential

  exact
    normalizedCompletedKernel_lawful
      (rateNormalizedKernel_completionStable_of_sequential
        hSeq)

/--
The same completion agrees with the canonical finite coupling.
-/
theorem normalizedCompletedKernel_of_sequential_agrees_finite
    (hSeq : RateNormalizedKernelSequentialControlled)
    (a b : PrimeTensor.MulRat) :
    (normalizedCompletedKernel_of_sequential hSeq).couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b := by

  unfold normalizedCompletedKernel_of_sequential

  exact
    normalizedCompletedKernel_agrees_finite
      (rateNormalizedKernel_completionStable_of_sequential
        hSeq)
      a b

end PrimePairApprox
end Bridge
end PrimeTensor
