import PrimeTensor.Bridge.KernelNormalizedCompletion
import PrimeTensor.Fluid.CouplingTailInput

/-!
# Final generic reduction for normalized concrete-kernel completion

The raw same-depth output-rate requirement has been removed.

The only remaining concrete analytic property is now tail-local continuity in
the finite inputs:

    CouplingTailInputScaleControl streamFiniteKernel.

If that property is proved, rate normalization supplies the output schedule,
completion stability follows, and the completed concrete kernel is lawful and
agrees with the canonical finite coupling automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The sole remaining local analytic control property for the concrete finite
stream kernel.
-/
def StreamFiniteKernelTailInputControlled : Prop :=
  PrimeTensor.CouplingTailInputScaleControl
    streamFiniteKernel

/--
Tail-local input continuity of the raw concrete kernel is enough to complete
the rate-normalized kernel.
-/
theorem rateNormalizedKernel_completionStable_of_tailInput
    (hInput : StreamFiniteKernelTailInputControlled) :
    PrimeTensor.IsCouplingCompletionStable
      streamFiniteKernel.rateNormalized := by

  exact
    streamFiniteKernel.rateNormalized_toCompletionStable_of_tailInputControl
      hInput

/--
Construct the completed normalized concrete kernel from the sole remaining
tail-local input continuity hypothesis.
-/
noncomputable def normalizedCompletedKernel_of_tailInput
    (hInput : StreamFiniteKernelTailInputControlled) :
    PrimeTensor.MulCoupling :=
  normalizedCompletedKernel
    (rateNormalizedKernel_completionStable_of_tailInput
      hInput)

/--
The resulting completed coupling is lawful.
-/
theorem normalizedCompletedKernel_of_tailInput_lawful
    (hInput : StreamFiniteKernelTailInputControlled) :
    PrimeTensor.IsMulCoupling
      (normalizedCompletedKernel_of_tailInput hInput) := by

  unfold normalizedCompletedKernel_of_tailInput

  exact
    normalizedCompletedKernel_lawful
      (rateNormalizedKernel_completionStable_of_tailInput
        hInput)

/--
The resulting completion agrees with the canonical finite coupling on embedded
finite barcodes.
-/
theorem normalizedCompletedKernel_of_tailInput_agrees_finite
    (hInput : StreamFiniteKernelTailInputControlled)
    (a b : PrimeTensor.MulRat) :
    (normalizedCompletedKernel_of_tailInput hInput).couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b := by

  unfold normalizedCompletedKernel_of_tailInput

  exact
    normalizedCompletedKernel_agrees_finite
      (rateNormalizedKernel_completionStable_of_tailInput
        hInput)
      a b

end PrimePairApprox
end Bridge
end PrimeTensor
