import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongCurlWeakEvolutionClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTCGlobalClosure

/-!
# Global continuation closure from the pressure-free curl weak FTC

The pressure-free curl/vorticity chain now proves, on every retained canonical
H³ tail and every strict elapsed interval inside the restart radius,

    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed.

`SelectedOldWeakStrongWeakFTCGlobalClosure` already packages the rest of the
weak--strong uniqueness argument:

    scalar old weak FTC
      -> selected/old physical agreement
      -> complete endpoint continuity
      -> H3ControlProducesExtension.

Thus the only remaining work here is quantifier packaging.  The local theorem
from `SelectedOldWeakStrongCurlWeakEvolutionClosure` is uniform in every
admissible energy bound, old preterminal solution, retained time, canonical H³
tail, elapsed restart interval, and strict endpoint condition.  It therefore
closes the global scalar weak-FTC frontier outright, and the existing global
closure theorem applies immediately.

This file adds no new analytic estimate.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

/-- The pressure-free curl/vorticity argument closes the global scalar
projected-RHS weak-FTC frontier. -/
theorem H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl :
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier := by
  intro E hE u T t hNS ht hTail

  intro q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_tailH3_curl
      hNS ht hqPos hEnd hE hTail

/-- Consequently the existing selected--old weak--strong chain closes the
formal `H3ControlProducesExtension` target from the canonical H³ tail alone. -/
theorem h3ControlProducesExtension_tailH3_curl :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroProjectedRHSWeakFTCClosed
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_tailH3_curl

end

end Euclidean
end Bridge
end PrimeTensor
