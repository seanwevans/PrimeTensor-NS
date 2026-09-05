import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Path

/-!
# Classicalization: endpoint canonical path initial state

The old-branch physical evolution frontier uses the endpoint-only canonical
spectral path generated from the retained H³ tail.  Before applying the general
variation-of-constants theorem, record its exact initial value.

At elapsed time zero, the canonical elapsed spectral state is the same weighted
H³ spectral state used as the restart anchor.  For positive overlap length,
normalizing the physical path and extending it back to real physical time
therefore also starts at that same anchor.

This is only representation and endpoint bookkeeping.  No continuity theorem,
mild identity, Fourier-mode ODE, forcing integrability, or new estimate is
proved here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalInitialState
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The H³ spectral encoder is independent of the particular proposition
witnesses used to establish integrability, measurability, and Fourier
compatibility at a fixed physical snapshot. -/
theorem velocityH3SpectralStateAt_eq_of_proof_irrel
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (s : ℝ)
    (hInt₁ hInt₂ : VelocityH3IntegrableAt u s)
    (hMeas₁ hMeas₂ : VelocityH3MeasurableAt u s)
    (hFourier₁ :
      VelocityH3FourierCompatibleAt u s hInt₁ hMeas₁)
    (hFourier₂ :
      VelocityH3FourierCompatibleAt u s hInt₂ hMeas₂) :
    velocityH3SpectralStateAt
        u s hInt₁ hMeas₁ hFourier₁
      =
    velocityH3SpectralStateAt
        u s hInt₂ hMeas₂ hFourier₂ := by
  have hInt : hInt₁ = hInt₂ :=
    Subsingleton.elim _ _
  subst hInt₂

  have hMeas : hMeas₁ = hMeas₂ :=
    Subsingleton.elim _ _
  subst hMeas₂

  have hFourier : hFourier₁ = hFourier₂ :=
    Subsingleton.elim _ _
  subst hFourier₂

  rfl

/-- The H³ spectral encoder also transports across equality of the physical
time parameter.  The dependent integrability/measurability/Fourier witnesses
are transported by `subst`, after which proof irrelevance closes the remaining
difference. -/
theorem velocityH3SpectralStateAt_eq_of_time_eq
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    {s₁ s₂ : ℝ}
    (hs : s₁ = s₂)
    (hInt₁ : VelocityH3IntegrableAt u s₁)
    (hInt₂ : VelocityH3IntegrableAt u s₂)
    (hMeas₁ : VelocityH3MeasurableAt u s₁)
    (hMeas₂ : VelocityH3MeasurableAt u s₂)
    (hFourier₁ :
      VelocityH3FourierCompatibleAt u s₁ hInt₁ hMeas₁)
    (hFourier₂ :
      VelocityH3FourierCompatibleAt u s₂ hInt₂ hMeas₂) :
    velocityH3SpectralStateAt
        u s₁ hInt₁ hMeas₁ hFourier₁
      =
    velocityH3SpectralStateAt
        u s₂ hInt₂ hMeas₂ hFourier₂ := by
  subst s₂
  exact
    velocityH3SpectralStateAt_eq_of_proof_irrel
      u s₁
      hInt₁ hInt₂
      hMeas₁ hMeas₂
      hFourier₁ hFourier₂

/-- The endpoint-only canonical physical path starts exactly at the retained
preterminal H³ spectral anchor. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_zero
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 ≤ tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail) :
    let q0 : Set.Icc (0 : ℝ) tau :=
      ⟨0, le_rfl, htau⟩
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
        hNS ht hEnd hE hTail hEndpoint q0
      =
    h3PreterminalCanonicalAnchorSpectralState
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
  dsimp only

  change
    h3PreterminalCanonicalSpectralStateOnElapsed
        hNS
        ht
        hEnd
        (canonicalH3TailDataFrom_integrableOnElapsed
          hEnd hTail)
        ⟨0, le_rfl, htau⟩
      =
    h3PreterminalCanonicalAnchorSpectralState
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1

  unfold h3PreterminalCanonicalSpectralStateOnElapsed
  unfold h3PreterminalCanonicalAnchorSpectralState

  apply velocityH3SpectralStateAt_eq_of_time_eq
  simp

/-- For positive overlap length, the globally indexed real-time extension of
the normalized endpoint-only canonical path has the same exact initial state. -/
theorem h3PreterminalTailCanonicalNormalizedPhysicalExtensionOfL2Endpoint_zero
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
        hNS ht hEnd hTail) :
    h3PathPhysicalRealExtension
        tau
        (h3SpectralNormalizedPathOfPhysical
          htau.le
          (h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
            hNS ht hEnd hE hTail hEndpoint))
        0
      =
    h3PreterminalCanonicalAnchorSpectralState
      hNS
      ht
      (canonicalH3TailDataFrom_at_anchor ht hTail).1 := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q0 : Set.Icc (0 : ℝ) tau :=
    ⟨0, le_rfl, htau.le⟩

  have hRecover :=
    h3PathPhysicalRealExtension_normalizedPhysical_apply
      htau P q0

  have hInitial :
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

  have hCombined :=
    hRecover.trans hInitial

  simpa only [P, q0] using hCombined

end

end Euclidean
end Bridge
end PrimeTensor
