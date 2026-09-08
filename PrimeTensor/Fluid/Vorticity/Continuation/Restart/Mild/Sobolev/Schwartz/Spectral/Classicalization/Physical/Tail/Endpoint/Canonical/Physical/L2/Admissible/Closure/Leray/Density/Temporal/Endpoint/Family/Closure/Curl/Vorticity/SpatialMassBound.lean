import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Endpoint.Canonical.Physical.L2.Admissible.Closure.Leray.Density.Temporal.Endpoint.Family.Closure.Curl.Vorticity.RHSMassYZ

/-!
# Uniform bounds for the actual endpoint vorticity temporal spatial masses

The pressure-free x/y/z vorticity RHS masses are now uniformly controlled on
every closed elapsed endpoint slice.  `RHSBridge` identifies the actual
zero-extended temporal-derivative spatial norm masses with those RHS masses at
strict preterminal times.

The only remaining normalization is scalar multiplication:

    ‖(lsmul ℝ ℝ) (ψ x) F(x)‖ = ‖ψ x‖ * ‖F(x)‖.

This file transfers the common RHS envelope back to the three scalar spatial
norm-mass functions used by `Integrable`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3EndpointCurlVorticitySpatialMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3EndpointCurlVorticitySpatialMassBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Uniform endpoint bound for the actual x-vorticity temporal spatial norm
mass. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_endpointH3
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
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
        hNS t ψ (q : ℝ)
      ≤
    h3EndpointVorticityRHSWeakMassEnvelope E ψ := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  rw [
    h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
      hNS ψ hs
  ]

  simpa only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    norm_mul
  ] using
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

/-- Uniform endpoint bound for the actual y-vorticity temporal spatial norm
mass. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_endpointH3
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
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
        hNS t ψ (q : ℝ)
      ≤
    h3EndpointVorticityRHSWeakMassEnvelope E ψ := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  rw [
    h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
      hNS ψ hs
  ]

  simpa only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    norm_mul
  ] using
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

/-- Uniform endpoint bound for the actual z-vorticity temporal spatial norm
mass. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_endpointH3
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
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
        hNS t ψ (q : ℝ)
      ≤
    h3EndpointVorticityRHSWeakMassEnvelope E ψ := by
  have hs :
      t + (q : ℝ) ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [ht.1, q.2.1]
    · linarith [hEnd, q.2.2]

  rw [
    h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_eq_rhs_of_mem
      hNS ψ hs
  ]

  simpa only [
    ContinuousLinearMap.lsmul_apply,
    smul_eq_mul,
    norm_mul
  ] using
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_endpointH3
      hNS ht hEnd hE hTail hEndpoint ψ q

/-- The three actual temporal spatial norm masses share the same uniform
endpoint H³ envelope. -/
theorem h3PreterminalWeakVorticityTemporalSpatialNormMassOnElapsed_le_endpointH3
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
    (ψ : H3WeakTestFunction)
    (q : Set.Icc (0 : ℝ) tau) :
    (
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed
          hNS t ψ (q : ℝ)
        ≤
      h3EndpointVorticityRHSWeakMassEnvelope E ψ
    )
      ∧
    (
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed
          hNS t ψ (q : ℝ)
        ≤
      h3EndpointVorticityRHSWeakMassEnvelope E ψ
    )
      ∧
    (
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed
          hNS t ψ (q : ℝ)
        ≤
      h3EndpointVorticityRHSWeakMassEnvelope E ψ
    ) := by
  exact
    ⟨
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q,
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q,
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_endpointH3
        hNS ht hEnd hE hTail hEndpoint ψ q
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
