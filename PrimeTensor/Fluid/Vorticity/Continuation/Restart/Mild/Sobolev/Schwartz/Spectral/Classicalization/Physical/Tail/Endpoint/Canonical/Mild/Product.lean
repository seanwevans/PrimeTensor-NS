import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Mild
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Fourier.L2.Duhamel.Identification.Product.Endpoint

/-!
# Endpoint canonical restarted mild equation from product integrability

The product-integrability route now reaches the actual weighted H³
variation-of-constants identity for every positive elapsed target
`q ∈ (0,tau]`.

This file packages that result into the normalized endpoint mild equation
consumed by the overlap machinery.

For a normalized time `s : H3UnitTime`, let

    q = h3PhysicalTime tau s.

There are only two cases:

* `q = 0`: heat at zero is the identity, the Duhamel term vanishes, and the
  endpoint physical path is exactly the retained spectral anchor;
* `q > 0`: since always `q ≤ tau`, the endpoint-safe product-integrability H³
  variation-of-constants theorem applies, including at `q = tau`.

Thus the old three Fourier-mode hypotheses are replaced by the single
all-divergence-free-tests temporal product-integrability frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalMildProduct
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The complete unit-viscosity restarted mild identity for the endpoint-only
canonical preterminal path follows from the all-tests temporal
product-integrability frontier. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_mild_of_all_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyProductIntegrableOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint) :
    ∀ s : H3UnitTime,
      h3SpectralVelocityHeatApplyNN
          1 zero_le_one
          (h3PhysicalTimeNN tau htau.le s)
          (h3PreterminalCanonicalAnchorSpectralState
            hNS
            ht
            (canonicalH3TailDataFrom_at_anchor ht hTail).1)
        -
      h3SpectralFinHeatLerayDuhamel
          1
          (h3PhysicalTime tau s)
          one_pos
          (h3PathPhysicalRealExtension
            tau
            (h3SpectralNormalizedPathOfPhysical
              htau.le
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
          (h3PathPhysicalRealExtension
            tau
            (h3SpectralNormalizedPathOfPhysical
              htau.le
              (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
                hNS ht hEnd hE hTail hEndpoint)))
        =
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint
        (h3PhysicalTimeMap tau htau.le s) := by
  intro s

  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let W : ℝ → H3SpectralVelocityState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  let q : ℝ :=
    h3PhysicalTime tau s

  have hqMem :
      q ∈ Set.Icc (0 : ℝ) tau := by
    dsimp only [q]
    exact h3PhysicalTime_mem_Icc htau.le s

  by_cases hq0 : q = 0

  · have hqNN :
        h3PhysicalTimeNN tau htau.le s = 0 := by
      apply Subtype.ext
      exact hq0

    let q0 : Set.Icc (0 : ℝ) tau :=
      ⟨0, le_rfl, htau.le⟩

    have hMapZero :
        h3PhysicalTimeMap tau htau.le s = q0 := by
      apply Subtype.ext
      exact hq0

    have hPzero :
        P q0
          =
        h3PreterminalCanonicalAnchorSpectralState
          hNS
          ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
      dsimp only [P, q0]
      exact
        h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_zero
          hNS ht htau.le hEnd hE hTail hEndpoint

    rw [hqNN]
    rw [h3SpectralVelocityHeatApplyNN_zero]
    rw [show h3PhysicalTime tau s = 0 by exact hq0]
    rw [h3SpectralFinHeatLerayDuhamel_zero]
    simp only [sub_zero]
    rw [hMapZero]

    exact hPzero.symm

  · have hqPos : 0 < q :=
      lt_of_le_of_ne
        hqMem.1
        (Ne.symm hq0)

    have hqTo :
        q ∈ Set.Ioc (0 : ℝ) tau :=
      ⟨hqPos, hqMem.2⟩

    have hVoC :=
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_variationOfConstants_of_all_productIntegrable_to
        hNS ht htau hEnd hE hTail hEndpoint hAll hqTo

    have hqNN :
        Real.toNNReal q
          =
        h3PhysicalTimeNN tau htau.le s := by
      rw [Real.toNNReal_of_nonneg hqPos.le]
      apply Subtype.ext
      rfl

    have hRecover :
        W q
          =
        P (h3PhysicalTimeMap tau htau.le s) := by
      dsimp only [W, q, P]
      exact
        h3PathPhysicalRealExtension_normalizedPhysical_apply
          htau
          (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint)
          (h3PhysicalTimeMap tau htau.le s)

    have hVoC' :
        W q
          =
        h3SpectralVelocityHeatApplyNN
            1 zero_le_one
            (h3PhysicalTimeNN tau htau.le s)
            (h3PreterminalCanonicalAnchorSpectralState
              hNS
              ht
              (canonicalH3TailDataFrom_at_anchor ht hTail).1)
          -
        h3SpectralFinHeatLerayDuhamel
          1 q one_pos W W := by
      simpa only [hqNN] using hVoC

    have hMild :=
      hVoC'.symm.trans hRecover

    simpa only [
      W,
      q,
      P,
      h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
    ] using hMild

/-- The local unit-viscosity physical-evolution package follows from endpoint
`L²` continuity plus the all-tests temporal product-integrability frontier. -/
theorem h3PreterminalTailPhysicalEvolutionAt_of_endpoint_all_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hAll :
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyProductIntegrableOnElapsed
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailPhysicalEvolutionAt
      one_pos
      hNS
      ht
      htau.le
      hEnd
      hE
      hTail := by
  refine ⟨hEndpoint, ?_⟩

  exact
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_mild_of_all_productIntegrable
      hNS
      ht
      htau
      hEnd
      hE
      hTail
      hEndpoint
      hAll

end

end Euclidean
end Bridge
end PrimeTensor
