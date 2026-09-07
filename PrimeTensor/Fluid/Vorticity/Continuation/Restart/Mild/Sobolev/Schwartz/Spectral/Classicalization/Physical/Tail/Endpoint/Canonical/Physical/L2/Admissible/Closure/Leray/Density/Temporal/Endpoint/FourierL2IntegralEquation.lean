import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2Evolution

/-!
# Physical L² temporal admissibility: explicit Fourier L² integral equation

The preceding endpoint Fourier-`L²` transport theorem expresses physical
Hilbert-space evolution as an interval integral of the zero-extended projected
Fourier `L²` right-hand side.

On every genuine elapsed slice that projected right-hand side has already been
identified with the quotient-safe spectral expression

    Δ̂_L² W(s) - P div(W(s) ⊗ W(s)).

This file makes that expression the named spectral RHS path, proves its strong
continuity and Bochner interval-integrability directly from the already-closed
projected-RHS path, and substitutes it into the endpoint evolution theorem.

The resulting equation is the exact quotient-safe analogue of the Fourier ODE
integrated in time:

    raw(W(τ)) - raw(W(0))
      = ∫₀^τ [Δ̂_L² W(s) - F̂_L²(W(s))] ds.

No representative is evaluated at a fixed frequency.  In particular, the
pointwise raw-Fourier continuity hypothesis used by the older scalar
variation-of-constants route does not appear.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2IntegralEquation
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The literal quotient-safe spectral RHS of the normalized endpoint path.

This is intentionally defined on ambient elapsed time.  Only its restriction
to `[0,τ]` is used below. -/
noncomputable def h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
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
    (s : ℝ) :
    H3SpectralFinVectorState :=
  fun i : Fin 3 =>
    h3SpectralScalarLaplacianRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) i)
      -
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau.le hEnd hE hTail hEndpoint s i

@[simp]
theorem h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real_apply
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
    (i : Fin 3) :
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s i
      =
    h3SpectralScalarLaplacianRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) i)
      -
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau.le hEnd hE hTail hEndpoint s i :=
  rfl

/-- On `[0,τ]`, the already-packaged projected Fourier `L²` RHS is exactly the
literal spectral Laplacian-minus-Leray-forcing path. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2Real_eq_spectral_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (hs : s ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s
      =
    h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint s := by
  funext i

  exact
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real_apply_of_mem_eq_spectral
      hNS ht htau hEnd hE hTail hEndpoint hs i

/-- The literal spectral RHS is strongly continuous on the closed physical
elapsed interval. -/
theorem continuousOn_h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
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
    ContinuousOn
      (h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint)
      (Set.Icc (0 : ℝ) tau) := by
  have hProjected :=
    continuousOn_h3PreterminalTailCanonicalProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint

  apply hProjected.congr
  intro s hs

  exact
    (h3PreterminalTailCanonicalProjectedRHSFourierL2Real_eq_spectral_of_mem
      hNS ht htau hEnd hE hTail hEndpoint hs).symm

/-- Consequently the literal spectral RHS is a genuine Bochner interval
integrand. -/
theorem h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real_intervalIntegrable
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
    IntervalIntegrable
      (h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint)
      volume
      (0 : ℝ)
      tau := by
  exact
    (continuousOn_h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
      hNS ht htau hEnd hE hTail hEndpoint).intervalIntegrable_of_Icc
        htau.le

/-- A physical `L²` endpoint evolution identity therefore becomes the literal
quotient-safe Fourier `L²` integral equation for the normalized endpoint
spectral path. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_intervalIntegral_spectralRHS_of_physicalL2Evolution
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
    (hEvolution :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
          hNS ht htau hEnd hTail
        =
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
        hNS ht htau hEnd hE hTail hEndpoint) :
    (fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint tau) i))
      -
    (fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint 0) i))
      =
    ∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s := by
  calc
    (fun i : Fin 3 =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint tau) i))
        -
      (fun i : Fin 3 =>
        h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint 0) i))
        =
      h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
        hNS ht htau hEnd hE hTail hEndpoint :=
          h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_projectedRHSBochnerIntegral_of_physicalL2Evolution
            hNS ht htau hEnd hE hTail hEndpoint hEvolution
    _ =
      ∫ s in (0 : ℝ)..tau,
        h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
          hNS ht htau hEnd hE hTail hEndpoint s := by
            unfold
              h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral

            apply intervalIntegral.integral_congr
            intro s hs

            have hsClosed :
                s ∈ Set.Icc (0 : ℝ) tau := by
              simpa only [Set.uIcc_of_le htau.le] using hs

            exact
              h3PreterminalTailCanonicalProjectedRHSFourierL2Real_eq_spectral_of_mem
                hNS ht htau hEnd hE hTail hEndpoint hsClosed

/-- The same integral equation with the elapsed-zero endpoint state replaced by
the retained H³ spectral anchor.  This is the convenient initial-value form for
the forthcoming quotient-safe semigroup argument. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityDifferenceFromAnchor_eq_intervalIntegral_spectralRHS_of_physicalL2Evolution
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
    (hEvolution :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2Hilbert
          hNS ht htau hEnd hTail
        =
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbert
        hNS ht htau hEnd hE hTail hEndpoint) :
    (fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint tau) i))
      -
    (fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalCanonicalAnchorSpectralState
          hNS ht
          (canonicalH3TailDataFrom_at_anchor ht hTail).1) i))
      =
    ∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s := by
  have hEq :=
    h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_intervalIntegral_spectralRHS_of_physicalL2Evolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution

  have hZero :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_zero
      hNS ht htau hEnd hE hTail hEndpoint

  rw [hZero] at hEq

  exact hEq

end

end Euclidean
end Bridge
end PrimeTensor
