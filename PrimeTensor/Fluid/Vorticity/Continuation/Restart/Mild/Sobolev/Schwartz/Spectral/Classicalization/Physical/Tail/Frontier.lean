import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Overlap.Gluing
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.TailFrontier

/-!
# Classicalization: physical tail frontier

The selected-overlap stack now separates the continuation problem into two
genuinely analytic statements.

First, the old H³ tail must evolve in the strong/mild class used by the
spectral uniqueness argument:

* every physical ordered H³ `L²` jet coordinate is strongly continuous;
* the canonical old-solution path satisfies the restarted heat--Leray mild
  identity.

This is exactly
`H3PreterminalTailPhysicalEvolutionOnRestartRadius`.

Second, once the canonical selected restart is glued to the old branch, that
piecewise real field must possess the classical PDE regularity required by the
continuation interface:

* a lifespan strictly beyond the selected restart radius;
* a pressure making the glued field preterminal Navier--Stokes;
* global spatial `C³`;
* continuous ordered third spatial jet on the extended interval.

The overlap agreement and selected-decoder matching are no longer analytic
inputs: `PhysicalTailOverlapGluing` already derives both from the first
frontier.

This file names the two remaining frontiers separately and proves that together
they imply `H3SchwartzCanonicalTailRestartClassicalization`, hence the original
H³ continuation target.  No claim is made here that either frontier follows
from the weaker base preterminal regularity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailFrontier
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Classical PDE/regularity package for the canonical selected-overlap glue at
one retained H³ tail.

Agreement with the old branch and decoder matching are deliberately absent:
they are already consequences of physical tail evolution. -/
def H3PreterminalTailCanonicalSelectedOverlapGlueRegularityAt
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∃
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ),
      t + h3FinHeatLerayRestartRadius ν E < S
        ∧
      PreterminalNavierStokes3
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail)
        p
        S
        ∧
      RealVelocitySpatialC3
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail)
        ∧
      RealVelocityThirdJetContinuousOn
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail)
        S

/-- Radius-wide strong/mild evolution frontier for every retained canonical H³
tail. -/
def H3PreterminalTailPhysicalEvolutionFrontier
    (ν : ℝ)
    (hν : 0 < ν) : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail

/-- Classical PDE/regularity frontier for the canonical selected-overlap glue
for every retained canonical H³ tail. -/
def H3PreterminalTailCanonicalSelectedOverlapGlueRegularityFrontier
    (ν : ℝ)
    (hν : 0 < ν) : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailCanonicalSelectedOverlapGlueRegularityAt
        hν hNS ht hE hTail

/-- The two physical tail frontiers close the corrected Schwartz spectral
classicalization statement.

The first frontier supplies overlap uniqueness, hence exact old-branch
agreement and selected-decoder matching for the canonical glue.  The second
supplies precisely the remaining lifespan/PDE/regularity fields. -/
theorem h3SchwartzCanonicalTailRestartClassicalization_of_physicalTailFrontiers
    {ν : ℝ}
    (hν : 0 < ν)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier ν hν)
    (hRegularity :
      H3PreterminalTailCanonicalSelectedOverlapGlueRegularityFrontier
        ν hν) :
    H3SchwartzCanonicalTailRestartClassicalization ν hν := by
  intro E hE u T t hNS ht hTail

  have hEvo :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail :=
    hEvolution E hE u T t hNS ht hTail

  obtain
    ⟨p, S, hS, hPDE, hSpatial, hThird⟩ :=
      hRegularity E hE u T t hNS ht hTail

  let v : SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3PreterminalTailCanonicalSelectedOverlapGlue
      hν hNS ht hE hTail

  have hAgree :
      RealRestartAgreesBeforeT u v T := by
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
        hν hNS ht hE hTail

  have hMatchCanonical :
      H3SpectralRestartDecoderMatches
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail)
        v
        t
        (h3FinHeatLerayRestartRadius ν E) := by
    exact
      h3PreterminalTailCanonicalSelectedOverlapGlue_decoderMatches
        hν hNS ht hE hTail hEvo

  dsimp only

  refine
    ⟨
      v,
      p,
      S,
      hS,
      hAgree,
      ?_,
      ?_,
      ?_,
      ?_
    ⟩

  · exact hPDE

  · exact hSpatial

  · exact hThird

  · simpa only [
      h3PreterminalTailCanonicalSelectedRestart,
      h3PreterminalTailCanonicalAnchorSpectralState,
      h3PreterminalCanonicalAnchorSpectralState
    ] using hMatchCanonical

/-- Consequently, the two explicit physical tail frontiers imply the original
H³ continuation theorem through the already-green tail classicalization
reduction. -/
theorem h3ControlProducesExtension_of_physicalTailFrontiers
    {ν : ℝ}
    (hν : 0 < ν)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier ν hν)
    (hRegularity :
      H3PreterminalTailCanonicalSelectedOverlapGlueRegularityFrontier
        ν hν) :
    H3ControlProducesExtension := by
  exact
    h3ControlProducesExtension_of_schwartzSpectralTailClassicalization
      hν
      (h3SchwartzCanonicalTailRestartClassicalization_of_physicalTailFrontiers
        hν hEvolution hRegularity)

end
end Euclidean
end Bridge
end PrimeTensor
