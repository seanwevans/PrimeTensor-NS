import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyPhysicalAgreement
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureOldFrontier

/-!
# Lift weak-energy uniqueness across the canonical restart radius

The derivative-free weak-energy argument has already been converted to
pointwise selected/old physical agreement on one fixed strict elapsed interval.

The existing old-pressure restart-radius frontier supplies, for every positive
elapsed endpoint `q`, the all-divergence-free old-pressure mass bound on
`[0,q]`.  The canonical pressure bound then upgrades this automatically to the
pressure-defect family required by the weak-energy argument.

Thus the new uniqueness proof closes the previously isolated radius-wide
physical-agreement frontier.  The existing decoder/overlap machinery can then
turn this into strong spectral-state continuity on every admissible elapsed
interval.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyRestartRadius
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Radius-wide old-pressure control closes radius-wide selected/old physical
agreement by the derivative-free weak-energy argument. -/
theorem h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_oldPressureWeakEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
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

  have hOldq :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail := by
    exact
      hOld
        qClosed
        (by simpa only [qClosed] using q.property.1)
        (by simpa only [qClosed] using hEnd)

  have hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail := by
    exact
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_oldPressure
        hNS ht hEnd hE hTail hOldq

  have hAgreement :=
    h3PreterminalSelectedPhysicalAgreementAt_of_weakEnergy
      (tau := (q : ℝ))
      (q := (q : ℝ))
      hNS
      ht
      q.property.1
      hEnd
      hE
      hTail
      q.property.2
      hPressure
      ⟨q.property.1, le_rfl⟩

  exact hAgreement

/-- On any strict elapsed interval inside the canonical restart radius, the
old canonical weighted-H³ spectral state is strongly continuous. -/
theorem h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_oldPressureWeakEnergy
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
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalCanonicalSpectralStateContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalSpectralStateContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
      (one_pos : (0 : ℝ) < 1)
      hNS ht htau hEnd hE hTail htauR
      (h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_oldPressureWeakEnergy
        hNS ht hE hTail hOld)

/-- Consequently the concrete physical zeroth/ordered-third `L²` endpoint
continuity used by the restart machinery also follows from the same old-pressure
frontier through weak-energy uniqueness. -/
theorem h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_oldPressureWeakEnergy
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
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalCanonicalL2EndpointContinuousOnElapsed
      hNS ht hEnd hTail := by
  exact
    h3PreterminalCanonicalL2EndpointContinuousOnElapsed_of_selectedPhysicalAgreement_pressureFree
      (one_pos : (0 : ℝ) < 1)
      hNS ht htau hEnd hE hTail htauR
      (h3PreterminalSelectedPhysicalAgreementOnRestartRadius_of_oldPressureWeakEnergy
        hNS ht hE hTail hOld)

end

end Euclidean
end Bridge
end PrimeTensor
