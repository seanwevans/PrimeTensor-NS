import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Unit.Viscosity.Frontier.Endpoint.Continuity.Zero.TemporalVelocityLipschitz

/-!
# Zeroth-order endpoint continuity: package the pressure-family frontier

`TemporalVelocityLipschitz` closes the local zeroth-order physical `L²`
Lipschitz target from one explicit remaining hypothesis:

    every compact smooth divergence-free weak test has uniformly bounded
    old-vs-canonical pressure-gradient-defect spatial mass on the elapsed
    interval.

This file lifts that local statement to the existing restart-radius and global
frontier hierarchy.

No new analysis is introduced here.  The purpose is to replace the obsolete
Fourier-increment frontier by the pressure-family mass frontier that the
endpoint-independent weak/Fubini argument actually consumes.

Consequently:

* radius-wide pressure-family control implies radius-wide zeroth `L²`
  Lipschitz control;
* global pressure-family control implies the existing global zeroth
  Lipschitz frontier;
* therefore it also implies the global zeroth continuity frontier;
* paired with the independent third-order continuity frontier, it closes the
  current unit-viscosity continuation reduction.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology InnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityZeroTemporalPressureFamilyFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Restart-radius version of the sole remaining hypothesis used by the
endpoint-independent zeroth-order temporal argument. -/
def H3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius
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
        H3PreterminalTailCanonicalZeroAllDivergenceFreeWeakTestsPressureGradientDefectMassUniformlyBoundedOnElapsed
          hNS ht hEnd hTail

/-- Radius-wide pressure-family mass control closes the existing radius-wide
zeroth-order physical `L²` Lipschitz frontier. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_pressureFamily
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hPressure :
      H3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius
        E u T t hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius
      E u T t hNS ht hE hTail := by
  intro q hqPos hEnd

  exact
    h3PreterminalCanonicalL2ZeroLipschitzOnElapsed_of_allDivergenceFreePressureDefect
      hNS ht hqPos hEnd hE hTail
      (hPressure q hqPos hEnd)

/-- Global unit-viscosity pressure-family mass frontier for the zeroth-order
endpoint-independent temporal argument. -/
def H3PreterminalTailUnitViscosityZeroPressureFamilyFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityZeroPressureFamilyFrontierOnRestartRadius
        E u T t hNS ht hE hTail

/-- The global pressure-family frontier implies the existing global
zeroth-order physical `L²` Lipschitz frontier. -/
theorem h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_pressureFamily
    (hPressure :
      H3PreterminalTailUnitViscosityZeroPressureFamilyFrontier) :
    H3PreterminalTailUnitViscosityZeroLipschitzFrontier := by
  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityZeroLipschitzFrontierOnRestartRadius_of_pressureFamily
      hNS ht hE hTail
      (hPressure E hE u T t hNS ht hTail)

/-- The global pressure-family frontier therefore closes the global
zeroth-order strong physical `L²` continuity frontier. -/
theorem h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_pressureFamily
    (hPressure :
      H3PreterminalTailUnitViscosityZeroPressureFamilyFrontier) :
    H3PreterminalTailUnitViscosityZeroContinuityFrontier := by
  exact
    h3PreterminalTailUnitViscosityZeroContinuityFrontier_of_lipschitz
      (h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_pressureFamily
        hPressure)

/-- Current continuation theorem with the entire zeroth-order branch reduced
to the explicit pressure-family mass frontier.  The independent ordered-third
continuity frontier remains the other input. -/
theorem h3ControlProducesExtension_of_unitViscosityZeroPressureFamilyThirdContinuityClosed
    (hPressure :
      H3PreterminalTailUnitViscosityZeroPressureFamilyFrontier)
    (hThird :
      H3PreterminalTailUnitViscosityThirdContinuityFrontier) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_unitViscosityZeroLipschitzThirdContinuityClosed
      (h3PreterminalTailUnitViscosityZeroLipschitzFrontier_of_pressureFamily
        hPressure)
      hThird

end

end Euclidean
end Bridge
end PrimeTensor
