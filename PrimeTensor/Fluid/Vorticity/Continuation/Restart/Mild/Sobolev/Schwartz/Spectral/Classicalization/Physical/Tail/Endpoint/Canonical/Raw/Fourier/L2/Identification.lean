import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Fin.Heat.Leray.Spectral.Round.Trip

/-!
# Classicalization: identify the endpoint canonical raw Fourier L² path

The previous checkpoint proves that exact H³ deweighting of each endpoint
canonical velocity coordinate is a continuous path in genuine Fourier `L²`.

This file identifies that quotient-safe path with the old solution's ordinary
zeroth-order Plancherel state.

At every elapsed physical time `q ∈ [0,τ]`, the canonical spectral slice is
literally the existing H³ encoder

    velocityH3SpectralStateAt u (t + q) ...

and the encoder/decoder round-trip theorem already proves

    rawFourierL2 (velocityH3SpectralScalarAt ...) =
      velocityH3BaseFourierAt ...

as equality of actual `L²` classes.

The same identity is then transported through normalization and real-time
extension on the physical interval.  No representative is evaluated at a
fixed frequency and no PDE identity is used.

This is the representation bridge needed before transporting the old
Navier--Stokes momentum equation into a quotient-safe Fourier `L²` evolution
equation.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology BigOperators

noncomputable section

noncomputable local instance axisFintypeH3PhysicalTailEndpointCanonicalRawFourierL2Identification
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- On the physical endpoint-canonical path, exact H³ deweighting is precisely
the old solution's zeroth-order Plancherel state at the corresponding physical
time. -/
theorem h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
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
    (q : Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
          hNS ht hEnd hE hTail hEndpoint q) i)
      =
    velocityH3BaseFourierAt
      u
      (t + (q : ℝ))
      (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail q)
      i := by
  rw [
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_apply
  ]

  rw [
    ← h3PreterminalTailCanonicalSpectralStateOnElapsed_eq
      hNS ht hEnd hTail q
  ]

  unfold h3PreterminalTailCanonicalSpectralStateOnElapsed
  unfold velocityH3SpectralStateAt

  exact
    h3SpectralScalarRawFourierL2_velocityH3SpectralScalarAt_eq
      (h3PreterminalTailFourierCompatibleOnElapsed
        hNS ht hEnd hTail q)
      i

/-- Inside the genuine physical interval, the globally indexed normalized
endpoint path has exactly the same quotient-safe raw Fourier `L²` state as the
old solution at physical time `t + s`. -/
theorem h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
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
    (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) i)
      =
    velocityH3BaseFourierAt
      u
      (t + s)
      (h3PreterminalTailIntegrableOnElapsed
        hEnd hTail ⟨s, hs⟩)
      (h3PreterminalTailMeasurableOnElapsed
        hNS ht hEnd hTail ⟨s, hs⟩)
      i := by
  let P : H3SpectralPhysicalVelocityPath tau :=
    h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint
      hNS ht hEnd hE hTail hEndpoint

  let q : Set.Icc (0 : ℝ) tau :=
    ⟨s, hs⟩

  have hRecover :
      h3PathPhysicalRealExtension
          tau
          (h3SpectralNormalizedPathOfPhysical htau.le P)
          (q : ℝ)
        =
      P q :=
    h3PathPhysicalRealExtension_normalizedPhysical_apply
      htau P q

  have hRecoverRaw :
      h3SpectralScalarRawFourierL2
          ((h3PathPhysicalRealExtension
            tau
            (h3SpectralNormalizedPathOfPhysical htau.le P)
            (q : ℝ)) i)
        =
      h3SpectralScalarRawFourierL2 ((P q) i) :=
    congrArg
      (fun U : H3SpectralFinVectorState =>
        h3SpectralScalarRawFourierL2 (U i))
      hRecover

  have hIdentify :
      h3SpectralScalarRawFourierL2 ((P q) i)
        =
      velocityH3BaseFourierAt
        u
        (t + (q : ℝ))
        (h3PreterminalTailIntegrableOnElapsed hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        i := by
    dsimp only [P]
    exact
      h3PreterminalTailCanonicalSpectralPhysicalPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
        hNS ht hEnd hE hTail hEndpoint q i

  have hCombined :=
    hRecoverRaw.trans hIdentify

  simpa only [
    P,
    q,
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
  ] using hCombined

end

end Euclidean
end Bridge
end PrimeTensor
