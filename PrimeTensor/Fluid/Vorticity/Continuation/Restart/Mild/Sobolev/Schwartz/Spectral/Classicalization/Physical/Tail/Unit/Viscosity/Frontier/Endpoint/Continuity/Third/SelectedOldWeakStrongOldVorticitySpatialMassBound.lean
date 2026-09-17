import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongOldVorticityRHSMassYZ

/-!
# Endpoint-independent old vorticity temporal spatial-mass bounds

The pressure-free x/y/z vorticity RHS masses are now uniformly controlled on
every closed elapsed slice directly from `CanonicalH3TailDataFrom`.

At strict preterminal times, the zero-extended temporal-derivative continuous
maps are pointwise identified with those pressure-free RHS components.  Hence

    ∫ ‖ψ(x) · ∂ₜωᵢ(t+q,x)‖ dx

inherits the same axis-independent envelope.

This is the endpoint-independent analogue of the older `SpatialMassBound`
bridge.  No endpoint continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongOldVorticitySpatialMassBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3SelectedOldWeakStrongOldVorticitySpatialMassBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Uniform bound for the actual x-vorticity temporal spatial norm mass,
directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
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
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSX_le_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

/-- Uniform bound for the actual y-vorticity temporal spatial norm mass,
directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
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
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSY_le_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

/-- Uniform bound for the actual z-vorticity temporal spatial norm mass,
directly from the canonical H³ tail. -/
theorem h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
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
    integral_weakTestNorm_mul_norm_h3LoggedPreterminalVorticityRHSZ_le_tailH3_weakStrong
      hNS ht hEnd hE hTail ψ q

/-- All three old vorticity temporal spatial norm masses share the same
endpoint-independent H³ envelope. -/
theorem h3PreterminalWeakVorticityTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
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
      h3PreterminalWeakVorticityXTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q,
      h3PreterminalWeakVorticityYTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q,
      h3PreterminalWeakVorticityZTemporalSpatialNormMassOnElapsed_le_tailH3_weakStrong
        hNS ht hEnd hE hTail ψ q
    ⟩

end

end Euclidean
end Bridge
end PrimeTensor
