import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Old.Vorticity.Temporal.Mass.Integrable
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.ProductIntegrable

/-!
# Endpoint-independent old vorticity product-space integrability

The scalar temporal spatial-norm-mass frontier is now closed directly from
`CanonicalH3TailDataFrom`, with no endpoint-continuity hypothesis.

The existing Carathéodory/Fubini reduction converts that scalar finiteness
statement into product-space integrability of all three compactly tested
zero-extended old-vorticity temporal derivatives.

No new estimate is introduced here; this file only removes the circular
endpoint hypothesis from the final product-integrability packaging theorem.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

/-- The canonical H³ tail alone closes the complete product-space
integrability requirement for the compactly tested x/y/z old-vorticity
temporal derivatives. -/
theorem H3PreterminalWeakVorticityTemporalProductIntegrableTo_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (ψ : H3WeakTestFunction) :
    H3PreterminalWeakVorticityTemporalProductIntegrableTo
      hNS t tau ψ := by
  exact
    H3PreterminalWeakVorticityTemporalProductIntegrableTo_of_spatialNormMassIntegrable
      hNS
      t
      tau
      ψ
      (H3PreterminalWeakVorticityTemporalSpatialNormMassIntegrableTo_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ)

end

end Euclidean
end Bridge
end PrimeTensor
