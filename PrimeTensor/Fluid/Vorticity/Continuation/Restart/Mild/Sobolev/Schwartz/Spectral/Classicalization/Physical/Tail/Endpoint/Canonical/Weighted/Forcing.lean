import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Variation.Of.Constants.Weighted.Forcing

/-!
# Classicalization: endpoint canonical weighted-forcing closure

The full endpoint-canonical mild package still exposes three positive-time
Fourier-mode hypotheses.  One of them is not an independent analytic
obligation.

At fixed output frequency and velocity coordinate, the weighted Leray forcing

    s ↦ exp (ν |2πξ|² s) • N̂(W(s), W(s))(ξ)

is interval integrable along any continuous H³ spectral path.  The endpoint
canonical normalized real path is already globally continuous, so its weighted
forcing is interval integrable on every finite interval automatically.

This file discharges that hypothesis from the local physical-evolution
constructor.  The remaining mode-side obligations are exactly:

* raw Fourier mode continuity;
* the finite heat--Leray mode ODE.

No new estimate, PDE identity, or Fourier representative theorem is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalWeightedForcing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The weighted fixed-frequency Leray forcing of the endpoint canonical real
path is interval integrable on every finite interval. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weightedForcing_intervalIntegrable
    {nu E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau a b : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (xi : H3FourierPoint3)
    (i : Fin 3) :
    IntervalIntegrable
      (fun s : ℝ =>
        Real.exp
            (nu * h3FourierGradientSquare xi * s)
          •
        h3RawFinLerayOuterProductDivergence
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s)
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau hEnd hE hTail hEndpoint) s)
          i xi)
      volume
      a
      b := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau hEnd hE hTail hEndpoint

  have hWcont : Continuous W := by
    dsimp only [W]
    exact
      continuous_h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
        hNS ht htau hEnd hE hTail hEndpoint

  exact
    h3RawFinLerayOuterProductDivergence_weighted_intervalIntegrable_of_continuous
      nu xi W W hWcont hWcont i a b

/-- Local endpoint physical evolution now depends only on raw-mode continuity
and the concrete heat--Leray mode ODE.

Weighted-forcing integrability is discharged from global path continuity. -/
theorem h3PreterminalTailPhysicalEvolutionAt_of_endpoint_mode_continuity_and_ODE
    {nu E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hnu : 0 < nu)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hFContinuous :
      ∀ q : ℝ,
        0 < q →
        q ≤ tau →
        ∀ xi : H3FourierPoint3, ∀ i : Fin 3,
          ContinuousOn
            (fun s : ℝ =>
              h3SpectralScalarRawFourier
                ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint) s i)
                xi)
            (Set.Icc (0 : ℝ) q))
    (hODE :
      ∀ xi : H3FourierPoint3,
        ∀ s ∈ Set.Ioo (0 : ℝ) tau,
          H3FinHeatLerayModeODEAt
            nu xi
            (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
              hNS ht htau.le hEnd hE hTail hEndpoint)
            s) :
    H3PreterminalTailPhysicalEvolutionAt
      hnu
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail := by
  apply
    h3PreterminalTailPhysicalEvolutionAt_of_endpoint_mode_data
      hnu
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hEndpoint
      hFContinuous
      hODE

  intro q hq hqTau xi i

  exact
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weightedForcing_intervalIntegrable
      (nu := nu)
      (E := E)
      (u := u)
      (T := T)
      (t := t)
      (tau := tau)
      (a := (0 : ℝ))
      (b := q)
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail
      hEndpoint
      xi
      i

end

end Euclidean
end Bridge
end PrimeTensor
