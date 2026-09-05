import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Unit.Viscosity.Incompressibility

/-!
# Unit-viscosity PDE frontier after incompressibility

`UnitViscosityIncompressibility` proves that the canonical local fill is
pointwise incompressible on every admissible local endpoint `S` satisfying

    S - t < h3FinHeatLerayRestartRadius 1 E.

The previous decomposed frontier still asks callers to supply that already
proved field.  This file removes it from the public continuation interface.

The remaining local PDE data are exactly:

* componentwise temporal `C¹`;
* spatial `C²` pressure regularity;
* the genuine mixed time/space `HasDerivAt` witness;
* the normalized unit-viscosity momentum equation.

The constructor below inserts incompressibility automatically from the same
radius bound already carried by the local continuation frontier.  Thus the
continuation theorem is reduced to physical-tail evolution plus these four
genuinely remaining PDE/regularity obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityPDEReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuinely remaining non-spatial local PDE fields after
incompressibility has been discharged. -/
structure H3PreterminalTailUnitViscosityLocalPDERemainderAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ) : Prop where

  velocity_temporal_one :
    H3PreterminalTailUnitViscosityVelocityTemporalRegularityAt
      hNS ht hE hTail S

  pressure_spatial_two :
    H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
      p S

  velocity_space_time_hasDerivAt :
    H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
      hNS ht hE hTail S

  momentum :
    H3PreterminalTailUnitViscosityMomentumAt
      hNS ht hE hTail p S

/-- Insert the now-proved incompressibility field into the previous five-field
component package. -/
theorem h3PreterminalTailUnitViscosityLocalPDEComponentsAt_of_remainder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hSR :
      S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hRemainder :
      H3PreterminalTailUnitViscosityLocalPDERemainderAt
        hNS ht hE hTail p S) :
    H3PreterminalTailUnitViscosityLocalPDEComponentsAt
      hNS ht hE hTail p S := by
  refine
    {
      velocity_temporal_one :=
        hRemainder.velocity_temporal_one
      pressure_spatial_two :=
        hRemainder.pressure_spatial_two
      velocity_space_time_hasDerivAt :=
        hRemainder.velocity_space_time_hasDerivAt
      incompressible := ?_
      momentum :=
        hRemainder.momentum
    }

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_incompressible
      hNS ht hE hTail hSR

/-- Local endpoint form of the reduced unit-viscosity PDE frontier.

The endpoint and pressure are unchanged from the previous frontier; only the
already-proved incompressibility field has disappeared from the supplied data.
-/
def H3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E →
    ∃
      (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
      (S : ℝ),
        T < S
          ∧
        S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E
          ∧
        H3PreterminalTailUnitViscosityLocalPDERemainderAt
          hNS ht hE hTail p S

/-- The four-field remainder frontier implies the previous five-field
component frontier by inserting physical incompressibility automatically. -/
theorem h3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt_of_remainder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hRemainder :
      H3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt
      hNS ht hE hTail := by
  intro hCross

  obtain
    ⟨p, S, hTS, hSR, hFields⟩ :=
      hRemainder hCross

  refine
    ⟨
      p,
      S,
      hTS,
      hSR,
      ?_
    ⟩

  exact
    h3PreterminalTailUnitViscosityLocalPDEComponentsAt_of_remainder
      hNS ht hE hTail hSR p hFields

/-- Direct reduced-frontier route to the local unit-viscosity PDE statement. -/
theorem h3PreterminalTailUnitViscosityLocalPDEAt_of_remainder
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hRemainder :
      H3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityLocalPDEAt
      hNS ht hE hTail := by
  exact
    h3PreterminalTailUnitViscosityLocalPDEAt_of_components
      hNS ht hE hTail
      hEvolution
      (h3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt_of_remainder
        hNS ht hE hTail hRemainder)

/-- Global four-field local-PDE frontier after incompressibility. -/
def H3PreterminalTailUnitViscosityLocalPDERemainderFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt
        hNS ht hE hTail

/-- The original H³ continuation theorem now needs physical-tail evolution and
only the four genuinely remaining local PDE/regularity fields. -/
theorem h3ControlProducesExtension_of_unitViscosityPDERemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hRemainder :
      H3PreterminalTailUnitViscosityLocalPDERemainderFrontier) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscosityPDEComponents
      hEvolution

  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt_of_remainder
      hNS ht hE hTail
      (hRemainder E hE u T t hNS ht hTail)

end
end Euclidean
end Bridge
end PrimeTensor
