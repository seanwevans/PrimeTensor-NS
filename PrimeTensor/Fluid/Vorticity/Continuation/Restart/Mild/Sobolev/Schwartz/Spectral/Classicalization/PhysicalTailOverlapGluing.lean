import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailEvolution
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedOverlapGluing

/-!
# Classicalization: physical tail overlap gluing

`PhysicalTailEvolution` proves that the canonical Banach-selected restart agrees
with the old preterminal H³ branch throughout their genuine overlap, assuming
the radius-wide physical evolution interface.

`SelectedOverlapGluing` already contains the exact piecewise real field:

    old logged velocity,       s < T
    selected restart velocity, T ≤ s.

This file specializes that glue to the canonical tail anchor and removes the
remaining overlap predicate from its API.

Under one `H3PreterminalTailPhysicalEvolutionOnRestartRadius` hypothesis, the
canonical glued real field therefore:

* agrees exactly with the old solution before `T`;
* realizes the canonical selected spectral decoder on the entire restart
  interval.

No regularity or Navier--Stokes equation for the glued field is proved here.
Those are the remaining classicalization obligations.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailOverlapGluing
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical real overlap glue obtained from the retained H³ tail anchor and
the Banach-selected restart launched there. -/
noncomputable def h3PreterminalTailCanonicalSelectedOverlapGlue
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
    (t := t)
    (T := T)
    hν
    u
    (h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail)
    (lt_of_lt_of_le zero_lt_one hE)
    (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail)

/-- The canonical tail glue agrees exactly with the original logged
preterminal velocity at every time before `T`. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    RealRestartAgreesBeforeT
      u
      (h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail)
      T := by
  unfold h3PreterminalTailCanonicalSelectedOverlapGlue

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedOverlapGlue_agreesBeforeT
      hν
      u
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)

/-- Radius-wide physical tail evolution makes the canonical glue realize the
selected spectral decoder throughout the full canonical restart interval. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_decoderMatches
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    H3SpectralRestartDecoderMatches
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail)
      (h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail)
      t
      (h3FinHeatLerayRestartRadius ν E) := by
  have hOverlap :
      H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
        (h3PreterminalTailCanonicalSelectedRestart
          hν hNS ht hE hTail)
        u
        t
        T
        (h3FinHeatLerayRestartRadius ν E) :=
    h3PreterminalTailCanonicalSelectedRestart_decoderAgreesOnOverlap
      hν hNS ht hE hTail hEvolution

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  have hOverlap' :
      H3SelectedRestartDecoderAgreesWithPreterminalOnOverlap
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀)
        u
        t
        T
        (h3FinHeatLerayRestartRadius ν E) := by
    simpa only [
      U₀,
      hEpos,
      hU₀,
      h3PreterminalTailCanonicalSelectedRestart
    ] using hOverlap

  have hMatch :
      H3SpectralRestartDecoderMatches
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hEpos hU₀)
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue
          (t := t)
          (T := T)
          hν
          u
          U₀
          hEpos
          hU₀)
        t
        (h3FinHeatLerayRestartRadius ν E) :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedOverlapGlue_decoderMatches
      hν
      u
      U₀
      hEpos
      hU₀
      hOverlap'

  simpa only [
    U₀,
    hEpos,
    hU₀,
    h3PreterminalTailCanonicalSelectedRestart,
    h3PreterminalTailCanonicalSelectedOverlapGlue
  ] using hMatch

/-- The two non-regularity conclusions needed by the tail classicalization
frontier are obtained simultaneously from the physical evolution interface. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_agreement_and_decoder
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail) :
    RealRestartAgreesBeforeT
        u
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail)
        T
      ∧
    H3SpectralRestartDecoderMatches
      (h3PreterminalTailCanonicalSelectedRestart
        hν hNS ht hE hTail)
      (h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail)
      t
      (h3FinHeatLerayRestartRadius ν E) := by
  exact
    ⟨
      h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
        hν hNS ht hE hTail,
      h3PreterminalTailCanonicalSelectedOverlapGlue_decoderMatches
        hν hNS ht hE hTail hEvolution
    ⟩

end
end Euclidean
end Bridge
end PrimeTensor
