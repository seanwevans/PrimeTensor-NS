import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyProductGronwall
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Closure
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureOldFrontier

/-!
# Global closure from temporal product integrability

The derivative-free selected--old weak-energy route has now been refactored so
that pressure is not part of its analytic interface.

The minimal old-branch hypothesis is the family-level temporal product
integrability needed to justify the weak FTC/Fubini step for every
divergence-free compact weak test.

This file packages that local hypothesis across the canonical restart radius
and then globally across every retained H³ tail.

The resulting chain is

    temporal product integrability on every restart subinterval
      -> selected/old physical agreement on the restart radius
      -> canonical zeroth/third physical L² endpoint continuity
      -> H3ControlProducesExtension.

Thus the endpoint weak--strong uniqueness branch is reduced to temporal product
integrability itself.  The older pressure frontier remains available only as a
sufficient way to produce this product-integrability frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyProductGlobalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radius-wide temporal product-integrability frontier.

For every positive elapsed endpoint inside the canonical unit-viscosity
restart radius, and every strict preterminal endpoint condition, all
divergence-free compact weak tests have the old temporal product integrability
needed by the pressure-free weak FTC. -/
def H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
    (E : ℝ)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀ q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius (1 : ℝ) E),
    ∀ hqPos : 0 < (q : ℝ),
      ∀ hEnd : t + (q : ℝ) < T,
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
          hNS ht hEnd hTail

/-- Global temporal product-integrability frontier for every retained
unit-viscosity canonical H³ tail. -/
def H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Radius-wide temporal product integrability gives radius-wide selected/old
physical agreement. -/
theorem h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_temporalProductIntegrability
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalSelectedPhysicalAgreementOnRestartRadius
      (1 : ℝ) E (one_pos : (0 : ℝ) < 1)
      u T t hNS ht hE hTail := by
  intro q hEnd

  let qClosed :
      Set.Icc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
    ⟨(q : ℝ), q.property.1.le, q.property.2⟩

  have hProductq :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail := by
    exact
      hProduct
        qClosed
        (by simpa only [qClosed] using q.property.1)
        (by simpa only [qClosed] using hEnd)

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_allTemporalProductIntegrable
      (tau := (q : ℝ))
      (q := (q : ℝ))
      hNS
      ht
      q.property.1
      hEnd
      hE
      hTail
      q.property.2
      hProductq
      ⟨q.property.1, le_rfl⟩

/-- Radius-wide product integrability closes the complete concrete physical
zeroth/ordered-third `L²` endpoint-continuity predicate on every strict elapsed
interval. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_temporalProductIntegrability
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
      (one_pos : (0 : ℝ) < 1)
      hNS ht htau hEnd hE hTail htauR
      (h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_temporalProductIntegrability
        hNS ht hE hTail hProduct)

/-- Global temporal product integrability supplies the complete zeroth-order
physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_temporalProductIntegrability
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier) :
    H3PreterminalTailUnitViscosityZeroContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  have hProductRadius :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hProduct E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail := by
    exact
      h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_temporalProductIntegrability
        (tau := (q : ℝ))
        hNS
        ht
        hqPos
        hEnd
        hE
        hTail
        q.property.2
        hProductRadius

  exact
    h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_endpoint
      hNS ht hEnd hTail hEndpoint

/-- Global temporal product integrability supplies the complete ordered-third
physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_temporalProductIntegrability
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  have hProductRadius :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hProduct E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail := by
    exact
      h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_temporalProductIntegrability
        (tau := (q : ℝ))
        hNS
        ht
        hqPos
        hEnd
        hE
        hTail
        q.property.2
        hProductRadius

  exact
    h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_endpoint
      hNS ht hEnd hTail hEndpoint

/-- Global continuation closure from temporal product integrability alone.

No old-pressure mass frontier is needed by this theorem. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroTemporalProductIntegrabilityClosed
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroThirdContinuityClosed
      (h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_temporalProductIntegrability
        hProduct)
      (h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_temporalProductIntegrability
        hProduct)

/-- The existing old-pressure frontier implies the new temporal-product
integrability frontier.  This keeps the older route as a backwards-compatible
sufficient condition while exposing the genuinely smaller analytic interface. -/
theorem h3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier_of_oldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier := by
  intro E hE u T t hNS ht hTail

  have hOldRadius :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hOld E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hOldq :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail := by
    exact
      hOldRadius q hqPos hEnd

  have hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail := by
    exact
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_oldPressure
        hNS ht hEnd hE hTail hOldq

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed_of_allPressureDefect
      hNS ht hEnd hE hTail hPressure

/-- Backwards-compatible factorization of the old-pressure closure through the
strictly smaller temporal-product frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressure_viaTemporalProductIntegrability
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroTemporalProductIntegrabilityClosed
      (h3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier_of_oldPressure
        hOld)

end

end Euclidean
end Bridge
end PrimeTensor
