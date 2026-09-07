import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Weak.Pairing.Primitive
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Projected.RHS.Pairing.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Weak.Velocity.Pairing.FTC.Reduction

/-!
# Physical L² temporal admissibility: integrate the weak temporal pairing

The replacement temporal route has now reached the precise Fubini frontier.

`PointwiseTemporalPrimitivePairing` proves

    <φ,W(q)> - <φ,W(0)>
      =
    Σᵢ ∫ₓ φᵢ(x) [∫₀^q ∂ₜWᵢ(r,x) dr] dx.

Independently, the existing pointwise projected-momentum analysis already proves
at every strict elapsed time `r ∈ (0,tau)` that

    Σᵢ ∫ₓ φᵢ(x) ∂ₜWᵢ(r,x) dx
      =
    weakProjectedRHSφ(r)

for divergence-free compact smooth `φ`.

This file integrates that latter identity in time on every shortened interval
`[0,q]`.  Endpoint values are irrelevant, so the open-interval congruence
theorem applies directly.

We then package the exact remaining analytic condition:

    Σᵢ ∫ₓ φᵢ(x) [∫₀^q ∂ₜWᵢ(r,x) dr] dx
      =
    ∫₀^q Σᵢ ∫ₓ φᵢ(x) ∂ₜWᵢ(r,x) dx.

Under only that Fubini equality, the weak evolution identity follows
immediately.  Thus the former local pointwise domination hypothesis has been
replaced by one explicit spacetime interchange statement, with all PDE and
endpoint bookkeeping already discharged.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3PhysicalL2TemporalEndpointTemporalPairingIntegral
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3PhysicalL2TemporalEndpointTemporalPairingIntegral :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- On every shortened elapsed interval, the time integral of the literal
compact-test temporal-derivative pairing equals the time integral of the
continuous projected weak RHS pairing.

No Fubini interchange is used here: both sides are already scalar functions of
time. -/
theorem intervalIntegral_h3PreterminalTailCanonicalWeakTemporalPairing_eq_projectedRHS_to
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    (∫ r in (0 : ℝ)..q,
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (temporal.d
              (fun s : ℝ =>
                (h3SpectralRealVelocityOfPath
                  (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                    hNS ht htau.le hEnd hE hTail hEndpoint)
                  s x).component
                    (h3AxisOfFin3 i))
              r)
          ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ r := by
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
      hNS ht htau.le hEnd hE hTail hEndpoint

  apply
    intervalIntegral.integral_congr_Ioo_of_le
      hq.1

  intro r hr

  have hrTau :
      r ∈ Set.Ioo (0 : ℝ) tau :=
    ⟨hr.1, hr.2.trans_le hq.2⟩

  have hrClosed :
      r ∈ Set.Icc (0 : ℝ) tau :=
    ⟨hrTau.1.le, hrTau.2.le⟩

  have hTemporal :=
    h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint_weakTemporalPairing_eq_weakProjectedRHSPairingOnElapsed
      hNS ht htau hEnd hE hTail hEndpoint
      hrTau φ hφ

  have hReal :=
    h3PreterminalTailCanonicalWeakProjectedRHSPairingReal_apply_of_mem
      hNS ht htau hEnd hE hTail hEndpoint
      φ hrClosed

  rw [hReal]

  simpa only [W] using hTemporal

/-- Exact remaining Fubini condition for one compact weak test and one
intermediate target.

This is intentionally an equality, not a hidden domination hypothesis.  The
next analytic increment will prove it from spacetime integrability. -/
def H3PreterminalTailCanonicalWeakTemporalFubiniTo
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector) : Prop :=
  (∑ i : Fin 3,
    ∫ x : Point3,
      (ContinuousLinearMap.lsmul ℝ ℝ)
        (φ i x)
        (∫ r in (0 : ℝ)..q,
          temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                s x).component
                  (h3AxisOfFin3 i))
            r)
      ∂volume)
    =
  ∫ r in (0 : ℝ)..q,
    ∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (temporal.d
            (fun s : ℝ =>
              (h3SpectralRealVelocityOfPath
                (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                  hNS ht htau.le hEnd hE hTail hEndpoint)
                s x).component
                  (h3AxisOfFin3 i))
            r)
        ∂volume

/-- Once the explicit Fubini equality holds, the full intermediate weak
projected evolution identity follows with no local-domination hypothesis. -/
theorem h3PreterminalTailCanonicalWeakVelocityPairingDifference_eq_intervalIntegral_to_of_temporalFubini
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hFubini :
      H3PreterminalTailCanonicalWeakTemporalFubiniTo
        hNS ht htau hEnd hE hTail hEndpoint
        (q := q) φ) :
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨q, hq⟩
      -
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
        hNS ht hEnd hTail φ
        ⟨0, ⟨le_rfl, htau.le⟩⟩
      =
    ∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
        hNS ht htau hEnd hE hTail hEndpoint φ r := by
  have hPrimitive :=
    h3PreterminalTailCanonicalVelocityWeakPairingDifference_eq_spatialIntegral_temporalPrimitive_to
      hNS ht htau hEnd hE hTail hEndpoint
      φ hq

  have hTemporal :=
    intervalIntegral_h3PreterminalTailCanonicalWeakTemporalPairing_eq_projectedRHS_to
      hNS ht htau hEnd hE hTail hEndpoint
      φ hφ hq

  calc
    h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ
          ⟨q, hq⟩
        -
      h3PreterminalTailCanonicalVelocityWeakPairingOnElapsed
          hNS ht hEnd hTail φ
          ⟨0, ⟨le_rfl, htau.le⟩⟩
        =
      ∑ i : Fin 3,
        ∫ x : Point3,
          (ContinuousLinearMap.lsmul ℝ ℝ)
            (φ i x)
            (∫ r in (0 : ℝ)..q,
              temporal.d
                (fun s : ℝ =>
                  (h3SpectralRealVelocityOfPath
                    (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                      hNS ht htau.le hEnd hE hTail hEndpoint)
                    s x).component
                      (h3AxisOfFin3 i))
                r)
          ∂volume :=
      hPrimitive
    _ =
      ∫ r in (0 : ℝ)..q,
        ∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (temporal.d
                (fun s : ℝ =>
                  (h3SpectralRealVelocityOfPath
                    (h3PreterminalTailCanonicalNormalizedRealPathOfL2Endpoint
                      hNS ht htau.le hEnd hE hTail hEndpoint)
                    s x).component
                      (h3AxisOfFin3 i))
                r)
            ∂volume :=
      hFubini
    _ =
      ∫ r in (0 : ℝ)..q,
        h3PreterminalTailCanonicalWeakProjectedRHSPairingReal
          hNS ht htau hEnd hE hTail hEndpoint φ r :=
      hTemporal

end

end Euclidean
end Bridge
end PrimeTensor
