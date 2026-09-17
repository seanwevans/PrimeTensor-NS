import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldWeakStrongWeakEnergyGronwall
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Third.SelectedOldL2DifferenceGronwall

/-!
# Convert weak-energy uniqueness to physical agreement

The derivative-free weak-energy argument now proves that the selected-minus-old
physical `L²` difference vanishes throughout a fixed elapsed interval.

The existing representation bridge
`h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero`
upgrades vanishing of that concrete `L²` difference at a positive elapsed time
to pointwise equality of the selected smooth classical velocity and the old
preterminal velocity.

This file performs exactly that final conversion.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace
  RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedOldWeakStrongWeakEnergyPhysicalAgreement
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Weak-energy uniqueness upgrades to pointwise selected/old physical
agreement at one strictly positive elapsed time. -/
theorem h3PreterminalSelectedPhysicalAgreementAt_of_weakEnergy
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t tau q : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (htau : 0 < tau)
    (hEnd : t + tau < T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (htauR :
      tau ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail)
    (hq : q ∈ Set.Ioc (0 : ℝ) tau) :
    H3PreterminalSelectedPhysicalAgreementAt
      (one_pos : (0 : ℝ) < 1)
      q
      hNS ht hE hTail := by
  let qClosed : Set.Icc (0 : ℝ) tau :=
    ⟨q, hq.1.le, hq.2⟩

  have hZero :
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed
        (one_pos : (0 : ℝ) < 1)
        hNS ht hEnd hE hTail qClosed
        =
      0 := by
    exact
      h3PreterminalSelectedOldVelocityPhysicalL2DifferenceOnElapsed_eq_zero_of_weakEnergy
        hNS ht htau hEnd hE hTail htauR hPressure qClosed

  have hqR :
      (qClosed : ℝ)
        ≤
      h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    simpa only [qClosed] using hq.2.trans htauR

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_l2Difference_eq_zero
      (one_pos : (0 : ℝ) < 1)
      hNS ht hEnd hE hTail
      qClosed
      (by simpa only [qClosed] using hq.1)
      hqR
      hZero

/-- On a fixed strict preterminal interval, the weak-energy argument supplies
pointwise physical agreement at every positive elapsed time. -/
theorem h3PreterminalSelectedPhysicalAgreementOnElapsed_of_weakEnergy
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    ∀ q : Set.Ioc (0 : ℝ) tau,
      H3PreterminalSelectedPhysicalAgreementAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
  intro q

  exact
    h3PreterminalSelectedPhysicalAgreementAt_of_weakEnergy
      hNS ht htau hEnd hE hTail htauR hPressure q.property

/-- The same fixed-interval result in selected-decoder form. -/
theorem h3PreterminalSelectedDecoderAgreementOnElapsed_of_weakEnergy
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
    (hPressure :
      H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
        hNS ht hEnd hTail) :
    ∀ q : Set.Ioc (0 : ℝ) tau,
      H3PreterminalSelectedDecoderAgreesAt
        (one_pos : (0 : ℝ) < 1)
        (q : ℝ)
        hNS ht hE hTail := by
  intro q

  exact
    h3PreterminalSelectedDecoderAgreesAt_of_physicalAgreement
      (one_pos : (0 : ℝ) < 1)
      (q : ℝ)
      hNS ht hE hTail
      (h3PreterminalSelectedPhysicalAgreementOnElapsed_of_weakEnergy
        hNS ht htau hEnd hE hTail htauR hPressure q)

end

end Euclidean
end Bridge
end PrimeTensor
