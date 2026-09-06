import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.WeakRHS
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.RHS.Bochner.Leray.Fixed
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Raw.Fourier.L2.Identification

/-!
# Physical L² temporal admissibility: quotient-safe Fourier L² integral evolution

The physical endpoint branch has two already-established quotient-safe
Plancherel bridges.

1. The raw Fourier vector of the physical velocity increment is exactly the
   difference of the raw Fourier vectors of the terminal and initial physical
   velocity states.

2. The raw Fourier vector of the physical Bochner-integrated projected RHS is
   exactly the Bochner integral of the strongly continuous Fourier `L²`
   projected RHS.

This file composes those bridges.

Thus any genuine physical Hilbert-space endpoint evolution identity

    U(τ) - U(0) = ∫₀^τ R(s) ds

immediately yields the exact quotient-safe spectral equation

    raw(W(τ)) - raw(W(0))
      =
    ∫₀^τ R̂_L²(s) ds.

No representative is evaluated at a fixed frequency.  In particular, this
theorem does not use the pointwise raw Fourier continuity assumption appearing
in the current scalar variation-of-constants route.

The result isolates the right replacement target for the remaining
PDE-to-mild bridge: prove the endpoint evolution directly in Fourier `L²`, then
derive a quotient-safe variation-of-constants statement at the `L²` level.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2Evolution
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointFourierL2Evolution :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The raw Fourier vector of the physical endpoint velocity state at elapsed
time `τ` is exactly exact H³ deweighting of the normalized endpoint path at
`τ`. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_tau_eq_normalizedRawFourierL2
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
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail
          ⟨tau, ⟨htau.le, le_rfl⟩⟩)
      =
    fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint tau) i) := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed

  simp only [PiLp.toLp_apply]

  calc
    h3ScalarFourierL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨tau, ⟨htau.le, le_rfl⟩⟩)
        =
      velocityH3BaseFourierAt
        u
        (t + tau)
        (h3PreterminalTailIntegrableOnElapsed
          hEnd hTail ⟨tau, ⟨htau.le, le_rfl⟩⟩)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail
          ⟨tau, ⟨htau.le, le_rfl⟩⟩)
        i := by
          rfl
    _ =
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint tau) i) := by
          symm
          exact
            h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
              hNS ht htau hEnd hE hTail hEndpoint
              tau
              ⟨htau.le, le_rfl⟩
              i

/-- The matching elapsed-zero physical velocity state has exactly the
normalized endpoint path's raw Fourier `L²` state at zero. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_zero_eq_normalizedRawFourierL2
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
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail
          ⟨0, ⟨le_rfl, htau.le⟩⟩)
      =
    fun i : Fin 3 =>
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint 0) i) := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed

  simp only [PiLp.toLp_apply]

  calc
    h3ScalarFourierL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          ⟨0, ⟨le_rfl, htau.le⟩⟩)
        =
      velocityH3BaseFourierAt
        u
        (t + 0)
        (h3PreterminalTailIntegrableOnElapsed
          hEnd hTail ⟨0, ⟨le_rfl, htau.le⟩⟩)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail
          ⟨0, ⟨le_rfl, htau.le⟩⟩)
        i := by
          rfl
    _ =
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint 0) i) := by
          symm
          simpa only [add_zero] using
            h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
              hNS ht htau hEnd hE hTail hEndpoint
              0
              ⟨le_rfl, htau.le⟩
              i

/-- Plancherel and Bochner commutation transport a genuine physical `L²`
endpoint evolution identity into the exact raw-Fourier-`L²` integral evolution
equation for the endpoint canonical path. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_projectedRHSBochnerIntegral_of_physicalL2Evolution
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
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral
      hNS ht htau hEnd hE hTail hEndpoint := by
  have hFourier :=
    congrArg
      h3PhysicalRealFinVectorL2HilbertRawFourier
      hEvolution

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_velocityIncrement_eq_sub
      hNS ht htau hEnd hTail,
    h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHS_eq
      hNS ht htau hEnd hE hTail hEndpoint,
    h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_tau_eq_normalizedRawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint,
    h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_zero_eq_normalizedRawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint
  ] at hFourier

  exact hFourier

/-- Coordinate form of the quotient-safe endpoint spectral integral evolution
equation.  The right-hand side is the actual Bochner integral of a continuous
Fourier `L²` path, not a fixed-frequency representative integral. -/
theorem h3PreterminalTailCanonicalRawFourierL2CoordinateDifference_eq_intervalIntegral_projectedRHS_of_physicalL2Evolution
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
        hNS ht htau hEnd hE hTail hEndpoint)
    (i : Fin 3) :
    h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint tau) i)
        -
      h3SpectralScalarRawFourierL2
          ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
            hNS ht htau.le hEnd hE hTail hEndpoint 0) i)
      =
    ∫ s in (0 : ℝ)..tau,
      h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s i := by
  have hVec :=
    h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_projectedRHSBochnerIntegral_of_physicalL2Evolution
      hNS ht htau hEnd hE hTail hEndpoint hEvolution

  have hi :=
    congrFun hVec i

  rw [
    h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegral_apply
      hNS ht htau hEnd hE hTail hEndpoint i
  ] at hi

  exact hi

/-- On a genuine elapsed slice, the ambient Fourier `L²` projected RHS is
literally the quotient-safe Laplacian minus quotient-safe Leray forcing of the
normalized endpoint spectral state. -/
theorem h3PreterminalTailCanonicalProjectedRHSFourierL2Real_apply_of_mem_eq_spectral
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
    (hs : s ∈ Set.Icc (0 : ℝ) tau)
    (i : Fin 3) :
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s i
      =
    h3SpectralScalarLaplacianRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint s) i)
      -
    h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2
      hNS ht htau.le hEnd hE hTail hEndpoint s i := by
  unfold
    h3PreterminalTailCanonicalProjectedRHSFourierL2Real

  rw [dif_pos hs]

  unfold
    h3PreterminalTailCanonicalProjectedRHSFourierL2OnElapsed

  rw [
    h3PreterminalTailCanonicalVelocityLaplacianFourierL2OnElapsed_eq_spectralLaplacian
      hNS ht htau hEnd hE hTail hEndpoint ⟨s, hs⟩ i
  ]

  rw [
    ← h3PreterminalTailCanonicalNormalizedRealLerayForcingFourierL2_eq_on_physical
      hNS ht htau hEnd hE hTail hEndpoint s hs i
  ]

end

end Euclidean
end Bridge
end PrimeTensor
