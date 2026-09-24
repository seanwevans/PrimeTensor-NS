import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.FTC.Energy.Gronwall
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Endpoint.Third.Selected.Old.Weak.Strong.Weak.Energy.Product.Global.Closure

/-!
# Global continuation closure from scalar old weak FTC

The weak--strong uniqueness route no longer needs coordinatewise spacetime
integrability of the strong old temporal derivative.

Its old-branch temporal interface has been reduced to the scalar
divergence-free projected-RHS weak FTC:

* interval integrability of
      r ↦ <φ, R_old(r)>;
* and
      <φ, O(q)-O(0)> = ∫₀^q <φ, R_old(r)> dr.

This file packages that condition across the canonical restart radius and then
globally across every retained canonical H³ tail.

The resulting hierarchy is

    old pressure frontier
      -> temporal product integrability
      -> scalar projected-RHS weak FTC
      -> selected/old physical agreement
      -> zeroth/third endpoint continuity
      -> H3ControlProducesExtension.

The main continuation theorem below assumes only the scalar weak-FTC frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakFTCGlobalClosure
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radius-wide scalar projected-RHS weak-FTC frontier. -/
def H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
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
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
          hNS ht hqPos hEnd hTail

/-- Global scalar projected-RHS weak-FTC frontier. -/
def H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- Radius-wide scalar weak FTC gives radius-wide selected/old physical
agreement. -/
theorem h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
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

  have hWeakFTCq :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed
        hNS ht q.property.1 hEnd hTail := by
    exact
      hWeakFTC
        qClosed
        (by simpa only [qClosed] using q.property.1)
        (by simpa only [qClosed] using hEnd)

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_allProjectedRHSWeakFTC
      (tau := (q : ℝ))
      (q := (q : ℝ))
      hNS
      ht
      q.property.1
      hEnd
      hE
      hTail
      q.property.2
      hWeakFTCq
      ⟨q.property.1, le_rfl⟩

/-- Radius-wide scalar weak FTC closes the complete concrete physical endpoint
continuity predicate on every strict elapsed interval. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_projectedRHSWeakFTC
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
    (hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
      (one_pos : (0 : ℝ) < 1)
      hNS ht htau hEnd hE hTail htauR
      (h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_projectedRHSWeakFTC
        hNS ht hE hTail hWeakFTC)

/-- Global scalar weak FTC supplies the zeroth-order physical `L²` continuity
frontier. -/
theorem h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_projectedRHSWeakFTC
    (hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    H3PreterminalTailUnitViscosityZeroContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  have hWeakFTCRadius :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hWeakFTC E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail := by
    exact
      h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_projectedRHSWeakFTC
        (tau := (q : ℝ))
        hNS
        ht
        hqPos
        hEnd
        hE
        hTail
        q.property.2
        hWeakFTCRadius

  exact
    h3PreterminalCanonicalL2ZeroContinuousOnElapsed_of_endpoint
      hNS ht hEnd hTail hEndpoint

/-- Global scalar weak FTC supplies the ordered-third physical `L²` continuity
frontier. -/
theorem h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_projectedRHSWeakFTC
    (hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    H3PreterminalTailUnitViscosityThirdContinuityFrontier := by
  intro E hE u T t hNS ht hTail

  have hWeakFTCRadius :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hWeakFTC E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hEndpoint :
      H3PreterminalCanonicalL2EndpointContinuousOnElapsed
        hNS ht hEnd hTail := by
    exact
      h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_projectedRHSWeakFTC
        (tau := (q : ℝ))
        hNS
        ht
        hqPos
        hEnd
        hE
        hTail
        q.property.2
        hWeakFTCRadius

  exact
    h3PreterminalCanonicalL2ThirdContinuousOnElapsed_of_endpoint
      hNS ht hEnd hTail hEndpoint

/-- Global continuation closure from scalar projected-RHS weak FTC alone. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroProjectedRHSWeakFTCClosed
    (hWeakFTC :
      H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroThirdContinuityClosed
      (h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_projectedRHSWeakFTC
        hWeakFTC)
      (h3PreterminalTailUnitViscosityThirdContinuityFrontier_of_projectedRHSWeakFTC
        hWeakFTC)

/-- The stronger temporal-product frontier implies the scalar weak-FTC
frontier. -/
theorem h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_temporalProductIntegrability
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier) :
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier := by
  intro E hE u T t hNS ht hTail

  have hProductRadius :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontierOnRestartRadius
        E u T t hNS ht hE hTail :=
    hProduct E hE u T t hNS ht hTail

  intro q hqPos hEnd

  have hProductq :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsTemporalProductIntegrableOnElapsed
        hNS ht hEnd hTail :=
    hProductRadius q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsProjectedRHSWeakFTCOnElapsed_of_allTemporalProductIntegrable
      hNS ht hqPos hEnd hTail hProductq

/-- Backwards-compatible factorization of the temporal-product closure through
the strictly smaller scalar weak-FTC frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroTemporalProductIntegrability_viaProjectedRHSWeakFTC
    (hProduct :
      H3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroProjectedRHSWeakFTCClosed
      (h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_temporalProductIntegrability
        hProduct)

/-- The old-pressure frontier also factors through the scalar weak-FTC
frontier via temporal product integrability. -/
theorem h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_oldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier := by
  exact
    h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_temporalProductIntegrability
      (h3PreterminalTailUnitViscosityZeroTemporalProductIntegrabilityFrontier_of_oldPressure
        hOld)

/-- Backwards-compatible old-pressure closure through the scalar weak-FTC
frontier. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressure_viaProjectedRHSWeakFTC
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroProjectedRHSWeakFTCClosed
      (h3PreterminalTailUnitViscosityZeroProjectedRHSWeakFTCFrontier_of_oldPressure
        hOld)

end

end Euclidean
end Bridge
end PrimeTensor
