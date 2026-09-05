import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Physical.Tail.Classical.Overlap

/-!
# Classicalization: spatial regularity of the canonical tail glue

`PhysicalTailClassicalOverlap` proves that the piecewise canonical glue is
literally the selected real restart throughout the whole positive restart
window `(t,t+R]`.

This file transports spatial `C³` regularity onto the glue in the two regions
where it is already available analytically:

* on every old preterminal slice `0 < s < T`, from the original classical
  preterminal Navier--Stokes solution;
* on every positive selected-window slice `t < s ≤ t+R`, from positive-time
  smoothing of the selected spectral restart.

The second statement crosses the branch point `T` automatically because the
classical-overlap theorem has already removed the `if` seam.

No claim is made here about arbitrary times after the exported restart radius.
That total-field packaging issue remains separate from the local continuation
regularity actually used near `T`.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailGlueSpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Before the old terminal time, the canonical glue inherits spatial `C³`
directly from the original preterminal Navier--Stokes branch. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_beforeT
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs : s ∈ Set.Ioo (0 : ℝ) T)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (fun y =>
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s y).component j) := by
  let p :
      SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  have hOld :
      SpatialC3
        (fun y =>
          (logSpaceTimeVectorField u s y).component j) :=
    hPDE.regularity.velocity_spatial_three
      s hs j

  have hAgree :
      logSpaceTimeVectorField u s
        =
      h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail s :=
    h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
      hν hNS ht hE hTail
      s hs

  have hFunctions :
      (fun y =>
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s y).component j)
        =
      (fun y =>
        (logSpaceTimeVectorField u s y).component j) := by
    funext y
    rw [← hAgree]

  rw [hFunctions]

  exact hOld

/-- Throughout the whole positive selected restart window, including across the
old terminal time `T`, the canonical glue inherits spatial `C³` from the
selected spectral restart. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_restartWindow
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (hs : t < s)
    (hsR :
      s - t ≤ h3FinHeatLerayRestartRadius ν E)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (fun y =>
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s y).component j) := by
  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  have hSelected :
      SpatialC3
        (fun y =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            hν U₀ hEpos hU₀ (s - t) y).component j) :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
      hν
      U₀
      hEpos
      hU₀
      (by linarith)
      hsR
      j

  have hEq :
      h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν U₀ hEpos hU₀ (s - t) := by
    simpa only [U₀, hEpos, hU₀] using
      h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_restartWindow
        hν hNS ht hE hTail hEvolution
        s hs hsR

  have hFunctions :
      (fun y =>
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s y).component j)
        =
      (fun y =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hEpos hU₀ (s - t) y).component j) := by
    funext y
    rw [hEq]

  rw [hFunctions]

  exact hSelected

/-- Compact local package: every slice in the union of the old preterminal
interval and the positive selected restart window is spatially `C³`. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_classicalRegion
    {ν E : ℝ}
    (hν : 0 < ν)
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionOnRestartRadius
        ν E hν u T t hNS ht hE hTail)
    (hs :
      s ∈ Set.Ioo (0 : ℝ) T
        ∨
      (t < s
        ∧
       s - t ≤ h3FinHeatLerayRestartRadius ν E))
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (fun y =>
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail s y).component j) := by
  rcases hs with hOld | hSelected

  · exact
      h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_beforeT
        hν hNS ht hE hTail hOld j

  · exact
      h3PreterminalTailCanonicalSelectedOverlapGlue_spatialC3At_restartWindow
        hν hNS ht hE hTail hEvolution
        hSelected.1 hSelected.2 j

end
end Euclidean
end Bridge
end PrimeTensor
