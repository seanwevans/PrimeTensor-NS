import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.TemporalMassIntegrable

/-!
# Product-space integrability of the endpoint vorticity temporal derivatives

`TemporalMassIntegrable` closes the final scalar finiteness condition isolated
by `Integrable`.  The existing Carathéodory/Fubini reduction therefore gives
product-space integrability of all three compactly tested zero-extended
vorticity temporal derivatives on the endpoint elapsed interval.

No new estimate is introduced in this file.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- The endpoint H³ tail estimate closes the complete product-space
integrability requirement for the compactly tested x/y/z vorticity temporal
derivatives. -/
theorem H3PreterminalWeakVorticityTemporalProductIntegrableTo_endpointH3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (ψ : H3WeakTestFunction) :
    H3PreterminalWeakVorticityTemporalProductIntegrableTo
      hNS t tau ψ := by
  exact
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
      hNS
      t
      tau
      ψ
      (H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ)

end

end Euclidean
end Bridge
end PrimeTensor
