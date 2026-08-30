import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailUnitViscosityFrontier

/-!
# Classicalization: decomposition of the unit-viscosity local PDE frontier

`PhysicalTailUnitViscosityFrontier` removes all continuation bookkeeping from
the final classicalization problem.  At unit viscosity, once an anchor is
chosen close enough to the old terminal time, it remains only to prove that
the locally filled canonical glue is a `PreterminalNavierStokes3` solution on
some interval `(0,S)` crossing `T`.

That statement still packages several logically independent analytic claims.
This file separates them.

Spatial `C³` is *not* among the new assumptions: it was already proved for the
filled field from physical-tail evolution.  The remaining fields of
`PreterminalNavierStokes3` are exactly:

* componentwise temporal `C¹` on `(0,S)`;
* the genuine mixed time/space `HasDerivAt` witness;
* spatial `C²` pressure regularity;
* incompressibility;
* the normalized unit-viscosity momentum equation.

A small constructor theorem reassembles those components into
`PreterminalNavierStokes3`.  Consequently the original H³ continuation theorem
is reduced to the already-isolated physical-tail evolution frontier plus these
four PDE/regularity tasks.

This checkpoint adds no analytic assumption beyond naming the fields that were
already hidden inside `H3PreterminalTailUnitViscosityLocalPDEAt`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationUnitViscosityPDEDecomposition
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Componentwise temporal `C¹` regularity of the locally filled canonical
selected-overlap velocity. -/
def H3PreterminalTailUnitViscosityVelocityTemporalRegularityAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (S : ℝ) : Prop :=
  ∀
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three),
      ContDiffOn
        ℝ 1
        (fun s : ℝ =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S s x).component j)
        (Set.Ioo (0 : ℝ) S)

/-- Genuine mixed time/space derivative witnesses for the locally filled
canonical selected-overlap velocity. -/
def H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (S : ℝ) : Prop :=
  ∀
    (s : ℝ),
      s ∈ Set.Ioo (0 : ℝ) S →
      ∀
        (x : Point3)
        (i j : PrimeTensor.Axis Depth.three),
          HasDerivAt
            (fun τ : ℝ =>
              spatial3.d
                i
                (fun y =>
                  (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                    hNS ht hE hTail S τ y).component j)
                x)
            (spatial3.d
              i
              (fun y =>
                temporal.d
                  (fun τ : ℝ =>
                    (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                      hNS ht hE hTail S τ y).component j)
                  s)
              x)
            s

/-- Spatial `C²` regularity of a candidate pressure on the local restart
interval. -/
def H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ) : Prop :=
  ∀ s : ℝ,
    s ∈ Set.Ioo (0 : ℝ) S →
      SpatialC2 (p s)

/-- Incompressibility of the locally filled canonical selected-overlap
velocity on `(0,S)`. -/
def H3PreterminalTailUnitViscosityIncompressibleAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (S : ℝ) : Prop :=
  ∀
    (s : ℝ),
      s ∈ Set.Ioo (0 : ℝ) S →
      ∀ x : Point3,
        PrimeTensor.Bridge.RealFluid.divergence
            spatial3
            (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
              hNS ht hE hTail S s)
            x
          =
        0

/-- Normalized unit-viscosity momentum equation for the locally filled
canonical selected-overlap velocity and a candidate pressure. -/
def H3PreterminalTailUnitViscosityMomentumAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ) : Prop :=
  ∀
    (s : ℝ),
      s ∈ Set.Ioo (0 : ℝ) S →
      ∀
        (x : Point3)
        (j : PrimeTensor.Axis Depth.three),
        (
          PrimeTensor.Bridge.RealFluid.temporalVectorDerivative
            temporal
            (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
              hNS ht hE hTail S)
            s x
        ).component j
          +
        (
          PrimeTensor.Bridge.RealFluid.advection
            spatial3
            (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
              hNS ht hE hTail S)
            s x
        ).component j
          =
        PrimeTensor.Bridge.RealFluid.pressureForceComponent
            spatial3 p s x j
          +
        (
          PrimeTensor.Bridge.RealFluid.laplacianVector
            spatial3
            (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
              hNS ht hE hTail S)
            s x
        ).component j

/-- The remaining non-spatial fields needed to build a local
`PreterminalNavierStokes3` witness. -/
structure H3PreterminalTailUnitViscosityLocalPDEComponentsAt
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

  incompressible :
    H3PreterminalTailUnitViscosityIncompressibleAt
      hNS ht hE hTail S

  momentum :
    H3PreterminalTailUnitViscosityMomentumAt
      hNS ht hE hTail p S

/-- Reassemble the exact `PreterminalNavierStokes3` structure.

The only field not taken from `hComponents` is spatial `C³`: that field is
already a theorem of the canonical local fill once physical-tail evolution is
available. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_preterminalNavierStokes3_of_components
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        (1 : ℝ) E
        (one_pos : (0 : ℝ) < 1)
        u T t hNS ht hE hTail)
    (hTS : T < S)
    (hSR :
      S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hComponents :
      H3PreterminalTailUnitViscosityLocalPDEComponentsAt
        hNS ht hE hTail p S) :
    PreterminalNavierStokes3
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
        hNS ht hE hTail S)
      p
      S := by
  have hSpatial :
      RealVelocitySpatialC3
        (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
          hNS ht hE hTail S) :=
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_spatialC3
      hNS ht hE hTail
      hEvolution hTS hSR

  refine
    {
      positive_terminal := ?_
      regularity := ?_
      incompressible := hComponents.incompressible
      momentum := hComponents.momentum
    }

  · exact
      lt_trans
        (lt_trans ht.1 ht.2)
        hTS

  · refine
      {
        velocity_spatial_three := ?_
        velocity_temporal_one := hComponents.velocity_temporal_one
        pressure_spatial_two := hComponents.pressure_spatial_two
        velocity_space_time_hasDerivAt :=
          hComponents.velocity_space_time_hasDerivAt
      }

    intro s hs j
    exact hSpatial s j

/-- Componentwise version of the local unit-viscosity PDE frontier.

The radius-crossing hypothesis chooses a local endpoint `S`, a pressure, and
the four remaining analytic component statements. -/
def H3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt
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
        H3PreterminalTailUnitViscosityLocalPDEComponentsAt
          hNS ht hE hTail p S

/-- The decomposed component frontier implies the previous opaque local PDE
frontier once physical-tail evolution supplies spatial `C³`. -/
theorem h3PreterminalTailUnitViscosityLocalPDEAt_of_components
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
    (hComponents :
      H3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityLocalPDEAt
      hNS ht hE hTail := by
  intro hCross

  obtain
    ⟨p, S, hTS, hSR, hFields⟩ :=
      hComponents hCross

  refine
    ⟨
      p,
      S,
      hTS,
      hSR,
      ?_
    ⟩

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_preterminalNavierStokes3_of_components
      hNS ht hE hTail
      hEvolution hTS hSR
      p hFields

/-- Global decomposed local-PDE frontier. -/
def H3PreterminalTailUnitViscosityLocalPDEComponentsFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscosityLocalPDEComponentsFrontierAt
        hNS ht hE hTail

/-- The original H³ continuation theorem now follows from physical-tail
evolution plus the four explicitly separated local PDE component tasks. -/
theorem h3ControlProducesExtension_of_unitViscosityPDEComponents
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hComponents :
      H3PreterminalTailUnitViscosityLocalPDEComponentsFrontier) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscosityPhysicalTailFrontiers
      hEvolution

  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityLocalPDEAt_of_components
      hNS ht hE hTail
      (hEvolution E hE u T t hNS ht hTail)
      (hComponents E hE u T t hNS ht hTail)

end
end Euclidean
end Bridge
end PrimeTensor
