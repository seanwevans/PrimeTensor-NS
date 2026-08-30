import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailGlueSpatialRegularity

/-!
# Classicalization: terminal third-jet continuity of the canonical tail glue

`PhysicalTailClassicalOverlap` removes the branch cut at the old terminal time
throughout the positive selected restart window.  In particular, if the
selected radius crosses the old terminal time,

    T - t < R,

then `T` lies strictly inside the open absolute-time window `(t,t+R)` on which
the canonical glue is exactly the selected real restart shifted by `t`.

The selected restart already has continuous ordered third spatial jet at every
strictly positive time strictly below `R`.  Continuity is local, so equality
with the glue on one neighborhood of `T` transfers that third-jet continuity
directly.

This is the terminal time-regularity statement actually required by
`H3ControlProducesRealRestart`; no full-radius or post-radius continuity
hypothesis is needed.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailGlueThirdJetContinuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- If the canonical selected restart radius crosses the old terminal time,
the canonical overlap glue has continuous complete third spatial jet at `T`. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_thirdJetContinuousAt_terminal
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
        ν E hν u T t hNS ht hE hTail)
    (hCross :
      T - t < h3FinHeatLerayRestartRadius ν E)
    (x : Point3) :
    RealVelocityThirdJetContinuousAt
      (h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail)
      T
      x := by
  intro a b c j

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  let hEpos : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  let hU₀ : ‖U₀‖ ≤ E :=
    norm_h3PreterminalTailCanonicalAnchorSpectralState_le
      hNS ht hE hTail

  let W :
      SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      hν U₀ hEpos hU₀

  have hElapsedPos :
      0 < T - t := by
    linarith [ht.2]

  have hSelectedThird :
      RealVelocityThirdJetContinuousAt
        W
        (T - t)
        x := by
    dsimp only [W]
    exact
      h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_thirdJetContinuousAt
        hν U₀ hEpos hU₀
        hElapsedPos
        hCross
        x

  have hRelative :
      ContinuousAt
        (fun r : ℝ =>
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (fun y =>
                  (W r y).component j)))
            x)
        (T - t) :=
    hSelectedThird a b c j

  have hShift :
      ContinuousAt
        (fun s : ℝ => s - t)
        T :=
    continuousAt_id.sub continuousAt_const

  have hAbsoluteComp :
      ContinuousAt
        ((fun r : ℝ =>
          spatial3.d
            a
            (spatial3.d
              b
              (spatial3.d
                c
                (fun y =>
                  (W r y).component j)))
            x)
          ∘
        (fun s : ℝ => s - t))
        T := by
    exact
      hRelative.comp_of_eq
        hShift
        rfl

  have hTWindow :
      T ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius ν E) := by
    constructor
    · exact ht.2
    · linarith

  have hWindowNhds :
      Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius ν E)
        ∈ 𝓝 T :=
    isOpen_Ioo.mem_nhds hTWindow

  have hEventually :
      (fun s : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (fun y =>
                (h3PreterminalTailCanonicalSelectedOverlapGlue
                  hν hNS ht hE hTail s y).component j)))
          x)
        =ᶠ[𝓝 T]
      ((fun r : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (fun y =>
                (W r y).component j)))
          x)
        ∘
      (fun s : ℝ => s - t)) := by
    filter_upwards [hWindowNhds] with s hs

    have hsR :
        s - t ≤ h3FinHeatLerayRestartRadius ν E := by
      linarith [hs.2]

    have hEq :
        h3PreterminalTailCanonicalSelectedOverlapGlue
            hν hNS ht hE hTail s
          =
        W (s - t) := by
      dsimp only [W, U₀, hEpos, hU₀]
      exact
        h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_restartWindow
          hν hNS ht hE hTail hEvolution
          s hs.1 hsR

    have hComponent :
        (fun y =>
          (h3PreterminalTailCanonicalSelectedOverlapGlue
            hν hNS ht hE hTail s y).component j)
          =
        (fun y =>
          (W (s - t) y).component j) := by
      funext y
      rw [hEq]

    rw [hComponent]

    rfl

  exact
    hAbsoluteComp.congr_of_eventuallyEq
      hEventually

/-- The same terminal third-jet continuity packaged for every spatial point. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_thirdJetContinuousAt_terminal_all
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
        ν E hν u T t hNS ht hE hTail)
    (hCross :
      T - t < h3FinHeatLerayRestartRadius ν E) :
    ∀ x : Point3,
      RealVelocityThirdJetContinuousAt
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          hν hNS ht hE hTail)
        T
        x := by
  intro x

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlue_thirdJetContinuousAt_terminal
      hν hNS ht hE hTail hEvolution hCross x

end
end Euclidean
end Bridge
end PrimeTensor
