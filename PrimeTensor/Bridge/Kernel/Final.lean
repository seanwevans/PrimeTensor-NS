import PrimeTensor.Bridge.Kernel.Sequential.Control

/-!
# Canonical completed logarithmic product coupling

All implementation details of the completed prime-pair kernel are hidden behind
one final coupling.

The construction is now unconditional:

* the rate-normalized stream kernel has concrete sequential control;
* hence it is completion-stable;
* its completion is a lawful multiplicative coupling;
* on embedded finite `MulRat` inputs it agrees with the canonical finite
  coupling.

Downstream developments should use `logProductCoupling` rather than carrying
normalization or completion-stability witnesses explicitly.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The canonical completed base-e logarithmic product coupling.
-/
noncomputable def logProductCoupling :
    PrimeTensor.MulCoupling :=
  normalizedCompletedKernel
    rateNormalizedKernel_completionStable

/--
The canonical completed coupling satisfies the multiplicative coupling laws.
-/
theorem logProductCoupling_lawful :
    PrimeTensor.IsMulCoupling logProductCoupling := by
  exact normalizedCompletedKernel_final_lawful

/--
On embedded finite multiplicative rationals, the completed coupling agrees
exactly with the canonical finite kernel.
-/
@[simp]
theorem logProductCoupling_ofRat
    (a b : PrimeTensor.MulRat) :
    logProductCoupling.couple
        (PrimeTensor.MulReal.ofRat a)
        (PrimeTensor.MulReal.ofRat b) =
      finiteKernel.couple a b := by
  exact
    normalizedCompletedKernel_final_agrees_finite
      a b

end PrimePairApprox
end Bridge
end PrimeTensor
