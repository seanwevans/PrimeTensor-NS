import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalPressureCanonicalBound

/-!
# Zeroth-order endpoint continuity: isolate the old-pressure frontier globally

The canonical pressure-gradient mass is now closed quantitatively from the H³
snapshot bound.  Therefore the only pressure quantity still needed by the
endpoint-independent zeroth-order route is the compact-test mass of the old
preterminal pressure gradient itself.

This file lifts that remaining local condition through the restart-radius and
global frontier hierarchy.

No new analytic estimate is introduced.  Its purpose is to make the remaining
obstruction exact:

    old preterminal pressure-gradient mass
      -> pressure-defect mass
      -> zeroth physical L² Lipschitz continuity
      -> zeroth endpoint continuity.

Thus, paired with the independent ordered-third continuity frontier, a global
old-pressure mass theorem is sufficient for the current continuation theorem.
The canonical pressure no longer appears as an assumption.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureOldFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Restart-radius form of the remaining old preterminal pressure-gradient
mass hypothesis. -/
def H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
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
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsOldPressureGradientMassUniformlyBoundedOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide old-pressure mass control implies the radius-wide pressure
defect family frontier; the canonical half is supplied by the proved H³
estimate. -/
theorem h3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius_of_oldPressure
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
    H3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed_of_oldPressure
      hNS ht hEnd hE hTail
      (hOld q hqPos hEnd)

/-- Radius-wide old-pressure mass control therefore closes the existing
radius-wide zeroth physical `L²` Lipschitz frontier. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_oldPressure
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
    H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  exact
    h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_pressureFamily
      hNS ht hE hTail
      (h3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius_of_oldPressure
        hNS ht hE hTail hOld)

/-- Global old preterminal pressure-gradient mass frontier. -/
def H3PreterminalTailUnitViscosityZeroOldPressureFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroOldPressureFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global old-pressure frontier implies the global pressure-defect family
frontier. -/
theorem h3PreterminalTailUnitViscosityZeroPressureFamilyFrontier_of_oldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityZeroPressureFamilyFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius_of_oldPressure
      hNS ht hE hTail
      (hOld E hE u T t hNS ht hTail)

/-- Hence the global old-pressure frontier closes the global zeroth physical
`L²` Lipschitz frontier. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_oldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontier := by
  exact
    h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_pressureFamily
      (h3PreterminalTailUnitViscosityZeroPressureFamilyFrontier_of_oldPressure
        hOld)

/-- And therefore it closes the global zeroth strong physical `L²`
continuity frontier. -/
theorem h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_oldPressure
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier) :
    H3PreterminalTailUnitViscosityZeroContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_lipschitz
      (h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_oldPressure
        hOld)

/-- Current continuation theorem with the entire zeroth-order branch reduced
to old preterminal pressure-gradient mass alone. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroOldPressureThirdContinuityClosed
    (hOld :
      H3PreterminalTailUnitViscosityZeroOldPressureFrontier)
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroLipschitzThirdContinuityClosed
      (h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_oldPressure
        hOld)
      hThird

end

end Euclidean
end Bridge
end PrimeTensor
