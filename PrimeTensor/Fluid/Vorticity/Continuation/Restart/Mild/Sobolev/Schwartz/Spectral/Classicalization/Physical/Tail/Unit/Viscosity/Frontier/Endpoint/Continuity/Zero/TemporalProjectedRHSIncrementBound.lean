import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalProjectedRHSBound

/-!
# Zeroth-order endpoint continuity: quantitative weak velocity increment bound

`TemporalProjectedRHSBound` proves the pointwise estimate

    |<phi, R(r)>|
      <=
    h3WeakTestVectorPhysicalL2L1Norm phi
      * h3UnitViscosityZeroRHSBound E

for the endpoint-independent physical projected RHS pairing.

Mathlib's constant-majorant interval-integral inequality now gives the explicit
time factor:

    |integral_0^q <phi, R(r)> dr|
      <=
    (h3WeakTestVectorPhysicalL2L1Norm phi
      * h3UnitViscosityZeroRHSBound E) * q.

Combining with `TemporalProjectedRHSFTC` gives the same bound for the complete
old velocity increment against every divergence-free compact smooth test whose
pressure-defect mass frontier supplies the Fubini step.

No endpoint `L2` continuity is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroProjectedRHSWeakIncrementBound
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroProjectedRHSWeakIncrementBound :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- The time integral of the endpoint-independent physical projected-RHS weak
pairing inherits the constant pointwise majorant with the exact elapsed-time
factor. -/
theorem norm_intervalIntegral_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_le
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hq : q ∈ Set.Icc (0 : ℝ) tau) :
    ‖∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r‖
      ≤
    (h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E)
      *
    q := by
  have hPointwise :
      ∀ᵐ r : ℝ ∂volume,
        r ∈ Set.uIoc (0 : ℝ) q →
          ‖h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
              hNS ht hEnd hTail φ r‖
            ≤
          h3WeakTestVectorPhysicalL2L1Norm φ
            *
          h3UnitViscosityZeroRHSBound E := by
    filter_upwards with r
    intro hr

    rw [Set.uIoc_of_le hq.1] at hr

    have hrTau :
        r ∈ Set.Icc (0 : ℝ) tau := by
      exact
        ⟨
          hr.1.le,
          hr.2.trans hq.2
        ⟩

    simpa only [Real.norm_eq_abs] using
      abs_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_le_of_mem
        hNS ht hEnd hE hTail φ hrTau

  have hBound :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae
      hPointwise

  simpa only [
    sub_zero,
    abs_of_nonneg hq.1
  ] using hBound

/-- Under the explicit pressure-defect mass frontier, every divergence-free
compact smooth test sees an old velocity increment bounded linearly in elapsed
time by the uniform physical projected-RHS ceiling. -/
theorem norm_h3PreterminalLoggedVelocity_weakPairingDifference_le_of_pressureDefect
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hPressure :
      H3PreterminalTailCanonicalZeroPressureGradientDefectSpatialNormMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail φ) :
    ‖∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume‖
      ≤
    (h3WeakTestVectorPhysicalL2L1Norm φ
      *
    h3UnitViscosityZeroRHSBound E)
      *
    q := by
  have hFTC :=
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
      hNS ht hEnd hE hTail φ hφ hq hPressure

  rw [hFTC]

  exact
    norm_intervalIntegral_h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_le
      hNS ht hEnd hE hTail φ hq

end

end Euclidean
end Bridge
end PrimeTensor
