import PrimeTensor.Bridge.KernelAsymptotic
import PrimeTensor.Fluid.CouplingAsymptoticCompletion

/-!
# Lawful completion of the normalized concrete kernel, conditional only on
# analytic completion stability

The concrete rate-normalized kernel already has:

* universal finite-output rate;
* finite unit and bilinear laws up to `MulAsymptotic`.

Therefore exact termwise algebra is no longer a completion obligation.

The sole remaining hypothesis in this file is
`IsCouplingCompletionStable streamFiniteKernel.rateNormalized`, i.e.

1. every normalized diagonal is Cauchy;
2. asymptotically equivalent input streams give asymptotically equivalent
   normalized diagonals.

Once that analytic condition is supplied, the completed concrete kernel is
lawful automatically.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
Complete the rate-normalized concrete kernel under the remaining analytic
completion-stability hypothesis.
-/
noncomputable def normalizedCompletedKernel
    (hStable :
      PrimeTensor.IsCouplingCompletionStable
        streamFiniteKernel.rateNormalized) :
    PrimeTensor.MulCoupling :=
  streamFiniteKernel.rateNormalized.complete hStable

/--
The completed normalized concrete kernel is lawful.  Exact termwise
bilinearity is not assumed.
-/
theorem normalizedCompletedKernel_lawful
    (hStable :
      PrimeTensor.IsCouplingCompletionStable
        streamFiniteKernel.rateNormalized) :
    PrimeTensor.IsMulCoupling
      (normalizedCompletedKernel hStable) := by

  change
    PrimeTensor.IsMulCoupling
      (
        streamFiniteKernel.rateNormalized.complete
          hStable
      )

  exact
    streamFiniteKernel.rateNormalized.complete_lawful_of_asymptotic
      (streamFiniteKernel.rateNormalized_hasUniversalOutputRate)
      rateNormalizedKernel_asymptotic_lawful
      hStable

/--
The normalized completion still agrees with the canonical finite coupling on
embedded finite barcodes.
-/
theorem normalizedCompletedKernel_agrees_finite
    (hStable :
      PrimeTensor.IsCouplingCompletionStable
        streamFiniteKernel.rateNormalized)
    (a b : PrimeTensor.MulRat) :
    (normalizedCompletedKernel hStable).couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b := by

  change
    (
      streamFiniteKernel.rateNormalized.complete
        hStable
    ).couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b

  exact
    streamFiniteKernel.rateNormalized.complete_agrees_finite
      finiteKernel
      rateNormalizedKernel_realizes_finiteKernel
      hStable
      a b

end PrimePairApprox
end Bridge
end PrimeTensor
