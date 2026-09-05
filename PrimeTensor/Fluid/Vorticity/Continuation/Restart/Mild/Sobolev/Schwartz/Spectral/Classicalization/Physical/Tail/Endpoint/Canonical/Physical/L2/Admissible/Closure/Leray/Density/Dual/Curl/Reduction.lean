import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Pairing

/-!
# Classicalization: reduce Leray density to weak-curl uniqueness

The dual density reduction exposed the following sufficient uniqueness theorem:

    a physical `L²` vector that is
    * Leray-fixed, and
    * orthogonal to every compact smooth divergence-free weak test

    must vanish.

`Dual.Curl.Pairing` has now extracted from the second hypothesis exactly the
three weak distributional curl-zero identities.

This file packages the resulting sharper frontier:

    Leray-fixed + weakly curl-free  ==>  zero.

If that statement is proved, then the original annihilator theorem follows
immediately, and hence so does the parameter-free physical Leray-density
frontier.

This is deliberately a structural checkpoint.  The next analytic task is now
completely isolated: prove the above uniqueness statement, most naturally by
transporting weak curl-freeness to Fourier space, combining it with the
Fourier divergence-free relation supplied by Leray-fixedness, and using
Plancherel nondegeneracy.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityDualCurlReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2AdmissibleClosureLerayDensityDualCurlReduction :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-! ## Exact weak-curl uniqueness frontier -/

/-- Exact remaining uniqueness theorem after extracting curl tests from the
full solenoidal annihilator hypothesis.

A physical three-component `L²` state must vanish if it lies in the exact
Leray-fixed submodule and is weakly curl-free. -/
def H3PhysicalL2LerayFixedWeakCurlFreeTrivial : Prop :=
  ∀ V : H3PhysicalRealFinVectorL2Hilbert,
    V ∈ h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule →
    H3PhysicalRealFinVectorL2HilbertWeakCurlFree V →
    V = 0

/-! ## Weak-curl uniqueness closes the original annihilator frontier -/

/-- The weak-curl uniqueness theorem implies the earlier trivial-annihilator
statement because annihilation of every divergence-free weak test already
forces weak curl-freeness. -/
theorem H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial_of_weakCurlFreeTrivial
    (hWeakCurl :
      H3PhysicalL2LerayFixedWeakCurlFreeTrivial) :
    H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial := by
  intro V hLeray hAnnihilates

  have hCurl :
      H3PhysicalRealFinVectorL2HilbertWeakCurlFree V :=
    h3PhysicalRealFinVectorL2Hilbert_weakCurlFree_of_annihilates_divergenceFreeWeakTests
      hAnnihilates

  exact
    hWeakCurl
      V
      hLeray
      hCurl

/-- Consequently, weak-curl uniqueness proves equality between the closed span
of compact smooth divergence-free weak tests and the exact physical Leray-fixed
submodule. -/
theorem h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule_of_weakCurlFreeTrivial
    (hWeakCurl :
      H3PhysicalL2LerayFixedWeakCurlFreeTrivial) :
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan
      =
    h3PhysicalRealFinVectorL2HilbertLerayFixedSubmodule := by
  exact
    h3DivergenceFreeWeakTestPhysicalL2ClosedSpan_eq_lerayFixedSubmodule_of_annihilatorTrivial
      (H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial_of_weakCurlFreeTrivial
        hWeakCurl)

/-- The exact parameter-free Leray-density frontier follows from weak-curl
uniqueness. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_weakCurlFreeTrivial
    (hWeakCurl :
      H3PhysicalL2LerayFixedWeakCurlFreeTrivial) :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_annihilatorTrivial
      (H3PhysicalL2LerayFixedDivergenceFreeWeakTestAnnihilatorTrivial_of_weakCurlFreeTrivial
        hWeakCurl)

end

end Euclidean
end Bridge
end PrimeTensor
