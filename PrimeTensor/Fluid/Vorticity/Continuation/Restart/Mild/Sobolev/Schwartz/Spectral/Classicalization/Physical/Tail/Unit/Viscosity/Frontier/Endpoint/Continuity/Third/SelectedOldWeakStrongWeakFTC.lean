import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongSelectedWeakFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakFTCReduction

/-!
# Close the selected--old weak FTC reduction

`SelectedOldWeakStrongWeakFTCReduction` already proved that

    selected weak FTC
      + endpoint-independent old weak FTC
      =>
    <Φ, S(q) - O(q)>
      =
    ∫₀^q <Φ, R_sel(r)> dr
      -
    ∫₀^q <Φ, R_old(r)> dr.

The selected branch hypothesis was the sole unfinished branch-local temporal
frontier.  `SelectedOldWeakStrongSelectedWeakFTC` now proves it outright.

This file simply discharges that hypothesis.  The resulting theorem requires
only:

* a divergence-free compact weak test;
* the old endpoint-independent temporal product-integrability assumption.

No strong old `L²` temporal derivative and no old endpoint continuity enter.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The selected-minus-old physical velocity difference satisfies the complete
weak evolution identity, with selected and old projected-RHS integrals kept
separate.  The only remaining temporal assumption is the endpoint-independent
old product-integrability input already used by the zeroth-order weak FTC. -/
theorem inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_selectedIntegral_sub_oldIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (q : Set.Icc (0 : ℝ) tau)
    (hOldProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t (q : ℝ) φ) :
    inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
          (one_pos : (0 : ℝ) < 1)
          hNS ht hEnd hE hTail q)
      =
    (∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalSelectedUnitProjectedRHSPhysicalL2HilbertRealOnElapsed
          hNS ht hE hTail htauR r))
      -
    (∫ r in (0 : ℝ)..(q : ℝ),
      inner ℝ
        (h3WeakTestVectorPhysicalL2Hilbert φ)
        (h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2HilbertReal
          hNS ht hEnd hTail r)) := by
  exact
    inner_h3WeakTestVectorPhysicalL2Hilbert_selectedOldDifference_eq_selectedIntegral_sub_oldIntegral
      hNS ht htau hEnd hE hTail htauR
      (h3PreterminalSelectedUnitWeakProjectedRHSFTCOnElapsed
        hNS ht htau hE hTail htauR)
      φ hφ q hOldProd

end

end Euclidean
end Bridge
end PrimeTensor
