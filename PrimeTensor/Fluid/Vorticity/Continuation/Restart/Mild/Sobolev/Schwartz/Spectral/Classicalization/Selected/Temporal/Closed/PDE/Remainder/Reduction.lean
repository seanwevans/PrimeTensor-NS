import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Temporal.Derivative.Frontier.Closure

/-!
# PDE remainder reduction after selected temporal closure

The selected temporal derivative frontier is now a theorem of the canonical
restart construction.  Therefore callers should no longer be asked to provide
that field as part of the local PDE remainder.

This file does not introduce another named frontier proposition.  Instead it
provides:

* a local constructor that inserts the proved selected temporal derivative
  field into `H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt`;
* a direct continuation theorem whose remaining supplied local data are exactly
  pressure spatial `C²`, mixed space-time `HasDerivAt`, and momentum.

Thus the public remainder has genuinely dropped from four supplied fields to
three without increasing the named `def ... : Prop` frontier count.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedTemporalClosedPDERemainderReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Insert the now-proved selected temporal derivative regularity into the
previous four-field selected derivative PDE remainder. -/
theorem h3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt_of_closedTemporal
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hPressure :
      H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
        p S)
    (hMixed :
      H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
        hNS ht hE hTail S)
    (hMomentum :
      H3PreterminalTailUnitViscosityMomentumAt
        hNS ht hE hTail p S) :
    H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt
      hNS ht hE hTail p S := by
  refine
    {
      selected_velocity_temporal_derivative := ?_
      pressure_spatial_two := hPressure
      velocity_space_time_hasDerivAt := hMixed
      momentum := hMomentum
    }

  exact
    h3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity_closed
      hNS ht hE hTail

/-- Direct continuation route after the selected temporal derivative field has
been discharged.

No new named frontier proposition is introduced here.  The second hypothesis
spells out exactly the three still-supplied local PDE fields. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedTemporalClosedPDERemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hRemainder :
      ∀
        (E : ℝ)
        (hE : 1 ≤ E)
        (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
        (T t : ℝ)
        (hNS : LoggedPreterminalNavierStokesAdmissible u T)
        (ht : t ∈ Set.Ioo (0 : ℝ) T)
        (hTail : CanonicalH3TailDataFrom u t T E),
          T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E →
          ∃
            (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
            (S : ℝ),
              T < S
                ∧
              S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E
                ∧
              H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
                p S
                ∧
              H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
                hNS ht hE hTail S
                ∧
              H3PreterminalTailUnitViscosityMomentumAt
                hNS ht hE hTail p S) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscositySelectedDerivativePDERemainder
      hEvolution

  intro E hE u T t hNS ht hTail
  intro hCross

  obtain
    ⟨
      p,
      S,
      hTS,
      hSR,
      hPressure,
      hMixed,
      hMomentum
    ⟩ :=
      hRemainder E hE u T t hNS ht hTail hCross

  refine
    ⟨
      p,
      S,
      hTS,
      hSR,
      ?_
    ⟩

  exact
    h3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt_of_closedTemporal
      hNS ht hE hTail
      p
      hPressure
      hMixed
      hMomentum

end

end Euclidean
end Bridge
end PrimeTensor
