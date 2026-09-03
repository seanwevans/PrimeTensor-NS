import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailCanonicalPath
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpectralEndpointPathContinuity

/-!
# Classicalization: endpoint-only physical H³ tail canonical path

`SpectralEndpointPathContinuity` shows that continuity of only the physical
zeroth and ordered third H³ `L²` jet coordinates is enough to make the complete
weighted spectral state continuous.

This file threads that reduced endpoint hypothesis through the canonical
preterminal path and overlap-witness constructor.

The resulting local overlap API has exactly two substantive analytic inputs:

1. physical `L²` continuity of the zeroth and ordered third jet coordinates;
2. the restarted heat--Leray mild identity.

First- and second-order physical jet continuity no longer appears in this API.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailEndpointCanonicalPath
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical weighted spectral-state map is continuous from only the
physical zeroth/third endpoint continuity hypothesis. -/
theorem h3PreterminalTailCanonicalSpectralStateContinuousOnElapsed_of_l2Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    Continuous
      (fun q : Set.Icc (0 : ℝ) τ =>
        h3PreterminalCanonicalSpectralStateOnElapsed
          hNS
          ht
          hEnd
          (canonicalH3TailDataFrom_integrableOnElapsed
            hEnd hTail)
          q) := by
  exact
    continuous_h3PreterminalCanonicalSpectralStateOnElapsed_of_l2Endpoint
      hNS ht hEnd hTail hEndpoint

/-- Canonical physical weighted-spectral path generated from endpoint-only
physical `L²` continuity. -/
noncomputable def h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    H3SpectralPhysicalVelocityPath τ :=
  h3PreterminalCanonicalSpectralPhysicalPath
    hNS
    ht
    hEnd
    hE
    (canonicalH3TailDataFrom_integrableOnElapsed
      hEnd hTail)
    (canonicalH3TailDataFrom_energyOnElapsed_le_twoE
      hE hEnd hTail)
    (h3PreterminalTailCanonicalSpectralStateContinuousOnElapsed_of_l2Endpoint
      hNS ht hEnd hTail hEndpoint)

@[simp]
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ E : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (q : Set.Icc (0 : ℝ) τ) :
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q
      =
    h3PreterminalCanonicalSpectralStateOnElapsed
      hNS
      ht
      hEnd
      (canonicalH3TailDataFrom_integrableOnElapsed
        hEnd hTail)
      q := by
  rfl

/-- Tail H³ data plus endpoint-only physical `L²` continuity reduce the local
preterminal overlap witness to the restarted mild equation alone. -/
theorem h3PreterminalSpectralOverlapWitnessAt_of_tailL2EndpointCanonicalPath
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t τ : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hτ : 0 ≤ τ)
    (hEnd : t + τ < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hMild :
      ∀ s : H3UnitTime,
        h3SpectralVelocityHeatApplyNN
            ν hν.le
            (h3PhysicalTimeNN τ hτ s)
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor
                ht hTail).1)
          -
        h3SpectralFinHeatLerayDuhamel
            ν
            (h3PhysicalTime τ s)
            hν
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                  hNS ht hEnd hE hTail hEndpoint)))
            (h3PathPhysicalRealExtension
              τ
              (h3SpectralNormalizedPathOfPhysical
                hτ
                (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                  hNS ht hEnd hE hTail hEndpoint)))
          =
        h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint
          (h3PhysicalTimeMap τ hτ s)) :
    H3PreterminalSpectralOverlapWitnessAt
      ν
      E
      hν
      (h3PreterminalCanonicalAnchorSpectralState
        hNS
        ht
        (canonicalH3TailDataFrom_at_anchor
          ht hTail).1)
      u
      t
      τ
      hτ := by
  let hCont :
      Continuous
        (fun q : Set.Icc (0 : ℝ) τ =>
          h3PreterminalCanonicalSpectralStateOnElapsed
            hNS
            ht
            hEnd
            (canonicalH3TailDataFrom_integrableOnElapsed
              hEnd hTail)
            q) :=
    h3PreterminalTailCanonicalSpectralStateContinuousOnElapsed_of_l2Endpoint
      hNS ht hEnd hTail hEndpoint

  apply
    h3PreterminalSpectralOverlapWitnessAt_of_tailCanonicalPath
      hν
      hNS
      ht
      hτ
      hEnd
      hE
      hTail
      hCont

  intro s

  simpa only [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint,
    hCont
  ] using hMild s

end
end Euclidean
end Bridge
end PrimeTensor
