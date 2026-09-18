import PrimeTensor.Fluid.Vorticity.H3.Energy.Estimate.Landau.Tail
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.WholeSpaceSobolev
import PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Analytic.Quartic.Closure

/-!
# Canonical Landau tail closure

The two whole-space analytic inputs previously threaded through the Landau tail
estimate are now theorems:

* `wholeSpaceC1FDerivL2ToL6_cutoff`;
* `wholeSpaceQuarticDerivativeIntegrationByParts_cutoff`.

This file removes those parameters from the public tail-growth interface.  The
remaining hypothesis is exactly the NS-specific tail package together with the
canonical H³ energy data.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set

/-- The Landau tail package canonically supplies the concrete H³ transport
control; the generic Sobolev and quartic IBP frontiers are discharged by the
cutoff theorems. -/
theorem h3TransportControlledOnTail_of_landauAnalytic_cutoff
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hData :
        CanonicalH3EnergyDataOnTail
          u a T
    )
    (
      hLandau :
        H3LandauTransportAnalyticOnTail
          u a T h
    ) :
    H3TransportControlledOnTail
      u a T h 4422 := by
  exact
    h3TransportControlledOnTail_of_landauAnalytic
      wholeSpaceC1FDerivL2ToL6_cutoff
      wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass
      hData
      hLandau

/-- Canonical H³ tail growth with no remaining generic whole-space analytic
hypotheses. -/
theorem h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic_cutoff
    {
      u :
        PrimeTensor.SpaceTimeVectorField
          ℝ ℝ PrimeTensor.MulReal Depth.three
    }
    {a T : ℝ}
    {h : ℝ → ℝ}
    (
      hClass :
        PreterminalH3EnergyClass
          u a T
    )
    (
      hData :
        CanonicalH3EnergyDataOnTail
          u a T
    )
    (
      hLandau :
        H3LandauTransportAnalyticOnTail
          u a T h
    ) :
    H3GradientGrowthInequalityFrom
      a T h
      (velocityH3EnergyAt u)
      4422 := by
  exact
    h3GradientGrowthInequalityFrom_canonical_of_landauAnalytic
      wholeSpaceC1FDerivL2ToL6_cutoff
      wholeSpaceQuarticDerivativeIntegrationByParts_cutoff
      hClass
      hData
      hLandau

end Euclidean
end Bridge
end PrimeTensor
