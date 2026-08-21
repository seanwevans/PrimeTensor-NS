import PrimeTensor.Bridge.Kernel.Agreement
import PrimeTensor.Fluid.Coupling.Asymptotic

/-!
# Asymptotic lawfulness of the rate-normalized concrete kernel

The raw concrete stream kernel realizes the already-lawful `finiteKernel`
exactly after quotienting.

Rate normalization changes only representative schedules, not quotient values.
Therefore the normalized concrete kernel inherits both finite algebra laws up
to `MulAsymptotic`.

This is the intrinsic replacement for the impossible requirement that
rate-normalized outputs remain exactly bilinear term by term.
-/

namespace PrimeTensor
namespace Bridge
namespace PrimePairApprox

/--
The rate-normalized concrete stream kernel still realizes exactly the canonical
finite quotient coupling.
-/
theorem rateNormalizedKernel_realizes_finiteKernel :
    PrimeTensor.RealizesFiniteCoupling
      streamFiniteKernel.rateNormalized
      finiteKernel := by

  exact
    streamFiniteKernel.rateNormalized_realizesFinite
      finiteKernel
      streamFiniteKernel_realizes_finiteKernel

/--
The rate-normalized concrete stream kernel satisfies the unit and bilinear laws
up to intrinsic asymptotic equivalence.
-/
theorem rateNormalizedKernel_asymptotic_lawful :
    PrimeTensor.IsAsymptoticStreamFiniteMulCoupling
      streamFiniteKernel.rateNormalized := by

  exact
    streamFiniteKernel.rateNormalized_asymptotic_lawful_of_realizesFinite
      finiteKernel
      streamFiniteKernel_realizes_finiteKernel
      finiteKernel_lawful

end PrimePairApprox
end Bridge
end PrimeTensor
