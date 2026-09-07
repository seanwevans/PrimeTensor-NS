import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.PhysicalL2FamilyClosure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.FourierL2EndpointEvolutionDerivative

/-!
# Physical L² temporal admissibility: transport the intermediate family to raw Fourier L²

`PhysicalL2FamilyClosure` proves, for every `q ∈ [0,tau]`, the genuine
physical Hilbert-space evolution identity

    U(q) - U(0) = ∫₀^q R(s) ds,

conditional only on the already-isolated generatorwise temporal-domination
frontier.

The quotient-safe variation-of-constants branch does not consume that physical
identity directly.  Its exact input is

`H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed`,

namely the family

    raw(W(q)) - raw(W(0))
      =
    ∫₀^q [Δ̂_L² W(s) - F̂_L²(W(s))] ds.

This file performs only that transport.

* identify the physical elapsed velocity state at arbitrary `q` with the raw
  Fourier state of the normalized endpoint path;
* transport the intermediate physical velocity increment through Plancherel;
* reuse the shortened physical-RHS/Fourier-Bochner identification already
  proved in `PhysicalL2FamilyClosure`;
* replace the zero-extended projected Fourier RHS by the literal spectral RHS
  on the shortened interval.

The final theorem has exactly the proposition required by the interaction/VOC
branch.  Thus the former ad hoc raw-Fourier evolution-family hypothesis is
derived from the single explicit temporal-domination frontier rather than
remaining an independent assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointFourierL2EvolutionFamily
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointFourierL2EvolutionFamily :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- At every elapsed target in the closed endpoint interval, the physical
zeroth-order Hilbert velocity state has exactly the raw Fourier state of the
normalized endpoint spectral path. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_to_eq_normalizedRawFourierL2
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
          hNS ht hEnd hTail q)
      =
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
      hNS ht htau.le hEnd hE hTail hEndpoint (q : ℝ) := by
  funext i

  unfold
    h3PhysicalRealFinVectorL2HilbertRawFourier
    h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
    h3SpectralFinVectorRawFourierL2

  simp only [PiLp.toLp_apply]

  calc
    h3ScalarFourierL2
        (h3PreterminalCanonicalL2JetOnElapsed
          hNS ht hEnd hTail
          (h3JetSlot0 i)
          q)
        =
      velocityH3BaseFourierAt
        u
        (t + (q : ℝ))
        (h3PreterminalTailIntegrableOnElapsed
          hEnd hTail q)
        (h3PreterminalTailMeasurableOnElapsed
          hNS ht hEnd hTail q)
        i := by
          rfl
    _ =
      h3SpectralScalarRawFourierL2
        ((h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
          hNS ht htau.le hEnd hE hTail hEndpoint (q : ℝ)) i) := by
          symm
          exact
            h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_rawFourierL2_eq_baseFourierAt
              hNS ht htau hEnd hE hTail hEndpoint
              (q : ℝ)
              q.property
              i

/-- Plancherel of the intermediate physical velocity increment is exactly the
raw Fourier endpoint-path increment from zero to `q`. -/
theorem h3PhysicalRealFinVectorL2HilbertRawFourier_velocityIncrementTo_eq_rawFourierL2Difference
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
    (q : Set.Icc (0 : ℝ) tau) :
    h3PhysicalRealFinVectorL2HilbertRawFourier
        (h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q)
      =
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint (q : ℝ)
      -
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
        hNS ht htau.le hEnd hE hTail hEndpoint 0 := by
  unfold h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo

  have hSub :
      h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap
          (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail q
            -
           h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
              hNS ht hEnd hTail
              ⟨0, ⟨le_rfl, htau.le⟩⟩)
        =
      h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap
          (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail q)
        -
      h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap
          (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
            hNS ht hEnd hTail
            ⟨0, ⟨le_rfl, htau.le⟩⟩) :=
    h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap.map_sub
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail q)
      (h3PreterminalCanonicalVelocityPhysicalL2HilbertOnElapsed
        hNS ht hEnd hTail
        ⟨0, ⟨le_rfl, htau.le⟩⟩)

  simpa only [
    h3PhysicalRealFinVectorL2HilbertRawFourierRealLinearMap_apply,
    h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_to_eq_normalizedRawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint q,
    h3PhysicalRealFinVectorL2HilbertRawFourier_endpointVelocity_to_eq_normalizedRawFourierL2
      hNS ht htau hEnd hE hTail hEndpoint
      ⟨0, ⟨le_rfl, htau.le⟩⟩
  ] using hSub

/-- One intermediate physical Hilbert evolution identity transports exactly to
the raw-Fourier-`L²` integral equation at that same target `q`. -/
theorem h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_intervalIntegral_spectralRHS_to_of_physicalL2Evolution
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
    (q : Set.Icc (0 : ℝ) tau)
    (hEvolution :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail q
        =
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
        hNS ht htau hEnd hE hTail hEndpoint q) :
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint (q : ℝ)
        -
      h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint 0
      =
    ∫ s in (0 : ℝ)..(q : ℝ),
      h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
        hNS ht htau hEnd hE hTail hEndpoint s := by
  have hFourier :=
    congrArg
      h3PhysicalRealFinVectorL2HilbertRawFourier
      hEvolution

  rw [
    h3PhysicalRealFinVectorL2HilbertRawFourier_velocityIncrementTo_eq_rawFourierL2Difference
      hNS ht htau hEnd hE hTail hEndpoint q,
    h3PhysicalRealFinVectorL2HilbertRawFourier_bochnerProjectedRHSTo_eq
      hNS ht htau hEnd hE hTail hEndpoint q
  ] at hFourier

  calc
    h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint (q : ℝ)
        -
      h3PreterminalTailCanonicalRawFourierL2VelocityReal
          hNS ht htau.le hEnd hE hTail hEndpoint 0
        =
      h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo
        hNS ht htau hEnd hE hTail hEndpoint q :=
      hFourier
    _ =
      ∫ s in (0 : ℝ)..(q : ℝ),
        h3PreterminalTailCanonicalSpectralProjectedRHSFourierL2Real
          hNS ht htau hEnd hE hTail hEndpoint s := by
            unfold
              h3PreterminalTailCanonicalProjectedRHSFourierL2BochnerIntegralTo

            apply intervalIntegral.integral_congr
            intro s hs

            have hsQ :
                s ∈ Set.Icc (0 : ℝ) (q : ℝ) := by
              simpa only [Set.uIcc_of_le q.property.1] using hs

            have hsTau :
                s ∈ Set.Icc (0 : ℝ) tau :=
              ⟨hsQ.1, hsQ.2.trans q.property.2⟩

            exact
              h3PreterminalTailCanonicalProjectedRHSFourierL2Real_eq_spectral_of_mem
                hNS ht htau hEnd hE hTail hEndpoint hsTau

/-- The exact raw-Fourier evolution-family hypothesis required by the
interaction/variation-of-constants branch follows from generatorwise temporal
local domination. -/
theorem H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed_of_all_temporallyLocallyDominated
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
      H3PreterminalTailCanonicalAllDivergenceFreeWeakTestsTemporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint) :
    H3PreterminalTailCanonicalRawFourierL2IntegralEvolutionOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint := by
  intro q hq

  let qI : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq⟩

  have hPhysical :
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo
          hNS ht htau hEnd hTail qI
        =
      h3PreterminalTailCanonicalProjectedRHSPhysicalL2BochnerIntegralHilbertTo
        hNS ht htau hEnd hE hTail hEndpoint qI := by
    exact
      h3PreterminalTailCanonicalVelocityIncrementPhysicalL2HilbertTo_eq_BochnerProjectedRHSTo_of_all_temporallyLocallyDominated
        hNS ht htau hEnd hE hTail hEndpoint hAll qI

  dsimp only [qI] at hPhysical

  exact
    h3PreterminalTailCanonicalRawFourierL2VelocityDifference_eq_intervalIntegral_spectralRHS_to_of_physicalL2Evolution
      hNS ht htau hEnd hE hTail hEndpoint
      ⟨q, hq⟩
      hPhysical

end

end Euclidean
end Bridge
end PrimeTensor
