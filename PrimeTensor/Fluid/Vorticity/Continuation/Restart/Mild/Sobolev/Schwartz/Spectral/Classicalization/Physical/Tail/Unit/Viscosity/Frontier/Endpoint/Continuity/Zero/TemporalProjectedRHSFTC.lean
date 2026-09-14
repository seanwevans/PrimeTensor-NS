import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalWeakFTC
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.RHSPhysicalWeak

/-!
# Zeroth-order endpoint continuity: old weak FTC with physical projected RHS

`TemporalWeakFTC` gives the complete three-coordinate compact-test velocity
increment identity in terms of the actual old temporal derivative.

For divergence-free compact smooth tests, `RHSPhysicalWeak` already proves
snapshot-by-snapshot that this temporal pairing is exactly the bounded physical
`L²` Leray-projected RHS pairing.  The pressure term therefore disappears at
the weak level.

This file combines those two endpoint-independent facts.  The old temporal
derivative appears only as the bridge used by FTC/Fubini; the final evolution
identity is

    weak velocity increment
      =
    integral of the physical projected-RHS weak pairing.

The pressure-gradient-defect mass frontier is retained only as one sufficient
condition for the product-space Fubini step.  It does not occur in the final
integrand.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroOldProjectedRHSWeakFTC
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

noncomputable local instance point3MeasureSpaceH3UnitViscosityZeroOldProjectedRHSWeakFTC :
    MeasureSpace Point3 :=
  @MeasureTheory.MeasureSpace.pi
    (PrimeTensor.Axis Depth.three)
    (Fintype.ofFinite (PrimeTensor.Axis Depth.three))
    (fun _ : PrimeTensor.Axis Depth.three => ℝ)
    (fun _ : PrimeTensor.Axis Depth.three => Real.measureSpace)

/-- Ambient-real extension of the endpoint-independent physical projected-RHS
weak pairing.  Only its restriction to the physical elapsed interval is used. -/
noncomputable def h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (r : ℝ) :
    ℝ :=
  if hr : r ∈ Set.Icc (0 : ℝ) tau then
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht hEnd hTail φ ⟨r, hr⟩
  else
    0

@[simp]
theorem h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau r : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hr : r ∈ Set.Icc (0 : ℝ) tau) :
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r
      =
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
      hNS ht hEnd hTail φ ⟨r, hr⟩ := by
  simp only [
    h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal,
    dite_eq_left hr
  ]

/-- Under product integrability, every divergence-free compact smooth test sees
the old velocity increment as the time integral of the exact physical projected
RHS pairing. -/
theorem h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_productIntegrable
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hEnd : t + tau < T)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (φ : H3WeakTestVector)
    (hφ : H3WeakTestVectorDivergenceFree φ)
    (hq : q ∈ Set.Icc (0 : ℝ) tau)
    (hProd :
      H3PreterminalLoggedVelocityTemporalProductIntegrableTo
        hNS t q φ) :
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r := by
  have hFTC :=
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hq hProd

  calc
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
        =
      ∫ r in (0 : ℝ)..q,
        ∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
                hNS i (t + r) x)
            ∂volume :=
      hFTC
    _ =
      ∫ r in (0 : ℝ)..q,
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
          hNS ht hEnd hTail φ r := by
      rw [intervalIntegral.integral_of_le hq.1]
      rw [intervalIntegral.integral_of_le hq.1]
      rw [← restrict_Ioo_eq_restrict_Ioc]
      apply integral_congr_ae

      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr

      have hrTau :
          r ∈ Set.Icc (0 : ℝ) tau := by
        exact
          ⟨
            hr.1.le,
            hr.2.le.trans hq.2
          ⟩

      have hAbs :
          t + r ∈ Set.Ioo (0 : ℝ) T := by
        constructor
        · linarith [ht.1, hr.1]
        · linarith [hEnd, hr.2, hq.2]

      rw [
        h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal_apply_of_mem
          hNS ht hEnd hTail φ hrTau
      ]

      have hWeak :=
        h3PreterminalLoggedVelocity_weakTemporalPairing_eq_zeroProjectedRHSPhysicalL2WeakPairingOnElapsed
          hNS ht hEnd hTail ⟨r, hrTau⟩ φ hφ

      calc
        (∑ i : Fin 3,
          ∫ x : Point3,
            (ContinuousLinearMap.lsmul ℝ ℝ)
              (φ i x)
              (h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension
                hNS i (t + r) x)
            ∂volume)
            =
          ∑ i : Fin 3,
            ∫ x : Point3,
              (ContinuousLinearMap.lsmul ℝ ℝ)
                (φ i x)
                (temporal.d
                  (fun a : ℝ =>
                    loggedVelocityComponent
                      u a (h3AxisOfFin3 i) x)
                  (t + r))
              ∂volume := by
                apply Finset.sum_congr rfl
                intro i hi
                apply integral_congr_ae
                filter_upwards with x
                rw [
                  h3LoggedPreterminalVelocityTemporalDerivativeContinuousMapExtension_apply_of_mem
                    hNS i hAbs x
                ]
        _ =
          h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingOnElapsed
            hNS ht hEnd hTail φ ⟨r, hrTau⟩ := by
              simpa only using hWeak

/-- The explicit pressure-defect mass frontier is therefore sufficient to
obtain the complete divergence-free projected-RHS weak evolution identity on
every shortened elapsed interval. -/
theorem h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_pressureDefect
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
    (∑ i : Fin 3,
      ∫ x : Point3,
        (ContinuousLinearMap.lsmul ℝ ℝ)
          (φ i x)
          (loggedVelocityComponent
              u (t + q) (h3AxisOfFin3 i) x
            -
          loggedVelocityComponent
              u t (h3AxisOfFin3 i) x)
        ∂volume)
      =
    ∫ r in (0 : ℝ)..q,
      h3PreterminalTailCanonicalZeroProjectedRHSPhysicalL2WeakPairingReal
        hNS ht hEnd hTail φ r := by
  apply
    h3PreterminalLoggedVelocity_weakPairingDifference_eq_projectedRHS_intervalIntegral_of_productIntegrable
      hNS ht hEnd hTail φ hφ hq

  exact
    H3PreterminalLoggedVelocityTemporalProductIntegrableTo_of_pressureDefect
      hNS ht hEnd hE hTail φ
      hq.1 hq.2 hPressure

end

end Euclidean
end Bridge
end PrimeTensor
