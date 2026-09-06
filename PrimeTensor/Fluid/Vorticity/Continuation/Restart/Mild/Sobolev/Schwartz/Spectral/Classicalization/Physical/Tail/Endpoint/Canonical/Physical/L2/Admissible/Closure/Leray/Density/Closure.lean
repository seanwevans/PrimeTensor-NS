import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Schwartz.Complex
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Algebra
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Dual.Curl.Fourier.Tempered

/-!
# Classicalization: close parameter-free physical L² Leray density

The two isolated Fourier obligations are now both proved.

* `Schwartz.Complex` proves

      weak physical curl-free
        -> tempered curl-free.

  `Fourier.Tempered` already upgrades this to Fourier curl-free almost
  everywhere.

* `Fourier.Algebra` proves

      Fourier divergence-free + Fourier curl-free
        -> zero.

The generic reduction in `Fourier.Reduction` then returns immediately to the
original physical statement:

    every Leray-fixed physical L² state belongs to the closed span of compact
    smooth divergence-free weak tests.

This file contains no new analytic estimate.  It is the closure node that
connects the completed compact-to-Schwartz bridge back to the density theorem
for which the entire curl argument was introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  SchwartzMap LineDeriv Distributions

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2AdmissibleClosureLerayDensityClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Close the weak-to-Fourier bridge -/

/-- Weak physical curl-freeness implies the almost-everywhere Fourier curl
identities. -/
theorem H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_proved :
    H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree := by
  exact
    H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_of_temperedBridge
      H3PhysicalL2WeakCurlFreeImpliesTemperedCurlFree_proved

/-! ## Close Leray-fixed weak-curl uniqueness -/

/-- A Leray-fixed physical `L²` state that is weakly curl-free is zero. -/
theorem H3PhysicalL2LerayFixedWeakCurlFreeTrivial_proved :
    H3PhysicalL2LerayFixedWeakCurlFreeTrivial := by
  exact
    H3PhysicalL2LerayFixedWeakCurlFreeTrivial_of_fourierBridge_of_spectralTrivial
      H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_proved
      H3SpectralFinDivergenceFreeCurlFreeTrivial_proved

/-! ## Final parameter-free physical L² density theorem -/

/-- Compact smooth divergence-free weak tests are dense in the physical
Leray-fixed `L²` subspace. -/
theorem H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_proved :
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan := by
  exact
    H3PhysicalL2LerayFixedSubmoduleContainedInDivergenceFreeWeakTestClosedSpan_of_fourierBridge_of_spectralTrivial
      H3PhysicalL2WeakCurlFreeImpliesFourierCurlFree_proved
      H3SpectralFinDivergenceFreeCurlFreeTrivial_proved

end

end Euclidean
end Bridge
end PrimeTensor
