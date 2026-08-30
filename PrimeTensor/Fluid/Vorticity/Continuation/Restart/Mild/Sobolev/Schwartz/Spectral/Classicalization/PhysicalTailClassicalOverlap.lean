import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailPointwiseOverlap

/-!
# Classicalization: exact classical overlap of the selected restart

`PhysicalTailPointwiseOverlap` upgrades the selected/preterminal overlap from
`L²` equality almost everywhere to pointwise equality of each spectral
coordinate.

This file completes the representation bookkeeping around that result.

First, the explicit maps

    Fin 3 → Axis Depth.three
    Axis Depth.three → Fin 3

are recorded as genuine two-sided inverses.

Second, coordinatewise pointwise overlap is packaged as equality of the whole
ordinary real velocity field at each positive overlap time.

Finally, the piecewise selected-overlap glue is shown to equal the selected
real restart on the *entire* positive restart window `(t,t+R]`.  Before `T`
this is the new pointwise uniqueness theorem; at and after `T` it is
definitionally the selected branch.

Thus the branch cut at `T` is invisible as a classical velocity field
throughout the positive selected window.  Later regularity and PDE transport
can work with the selected solution there instead of analyzing an `if` seam.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationPhysicalTailClassicalOverlap
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The project-wide `Fin 3 → Axis Depth.three` decoder is also a left inverse
of the explicit classicalization coordinate map. -/
@[simp]
theorem h3AxisOfFin3_h3ClassicalizationFinOfAxis
    (j : PrimeTensor.Axis Depth.three) :
    h3AxisOfFin3 (h3ClassicalizationFinOfAxis j) = j := by
  cases j with
  | first =>
      rfl
  | next j =>
      cases j with
      | first =>
          rfl
      | next j =>
          cases j with
          | first =>
              rfl

/-- On every strictly positive genuine overlap slice, the whole selected
ordinary real velocity field equals the old logged preterminal velocity. -/
theorem h3PreterminalTailCanonicalSelectedRestart_eq_old_on_positiveOverlap
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
    (q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E))
    (hq : 0 < (q : ℝ))
    (hBefore : t + (q : ℝ) < T) :
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
        hν
        (h3PreterminalTailCanonicalAnchorSpectralState
          hNS ht hTail)
        (lt_of_lt_of_le zero_lt_one hE)
        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
          hNS ht hE hTail)
        (q : ℝ)
      =
    logSpaceTimeVectorField
      u
      (t + (q : ℝ)) := by
  funext x

  apply tensor_eq_of_component_eq

  intro j

  let i : Fin 3 :=
    h3ClassicalizationFinOfAxis j

  have hAxis :
      h3AxisOfFin3 i = j := by
    dsimp only [i]
    exact
      h3AxisOfFin3_h3ClassicalizationFinOfAxis j

  have hComponent :=
    h3PreterminalTailCanonicalSelectedRestart_component_apply_eq_old_on_positiveOverlap
      hν hNS ht hE hTail hEvolution
      q hq hBefore i x

  simpa only [hAxis] using hComponent

/-- On a positive overlap slice the canonical piecewise glue is exactly the
selected real restart, even though its definition chooses the old branch there. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_positiveOverlap
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
    (q : Set.Icc
      (0 : ℝ)
      (h3FinHeatLerayRestartRadius ν E))
    (hq : 0 < (q : ℝ))
    (hBefore : t + (q : ℝ) < T) :
    h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail
        (t + (q : ℝ))
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      hν
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      (q : ℝ) := by
  have hSelectedOld :=
    h3PreterminalTailCanonicalSelectedRestart_eq_old_on_positiveOverlap
      hν hNS ht hE hTail hEvolution
      q hq hBefore

  unfold h3PreterminalTailCanonicalSelectedOverlapGlue
  unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue

  funext x

  simp only [dite_eq_left hBefore]

  exact congrFun hSelectedOld.symm x

/-- The branch cut at `T` disappears on the whole positive selected restart
window.

For any absolute time `s` with `t < s` and elapsed time `s-t ≤ R`, the
canonical glue is exactly the selected real restart evaluated at elapsed time
`s-t`, regardless of whether `s` lies before or after the old terminal time. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_restartWindow
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
    (s : ℝ)
    (hs : t < s)
    (hsR :
      s - t ≤ h3FinHeatLerayRestartRadius ν E) :
    h3PreterminalTailCanonicalSelectedOverlapGlue
        hν hNS ht hE hTail s
      =
    h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
      hν
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      (s - t) := by
  by_cases hBefore : s < T

  · let q :
        Set.Icc
          (0 : ℝ)
          (h3FinHeatLerayRestartRadius ν E) :=
      ⟨
        s - t,
        by linarith,
        hsR
      ⟩

    have hq :
        0 < (q : ℝ) := by
      dsimp only [q]
      linarith

    have hBeforeQ :
        t + (q : ℝ) < T := by
      dsimp only [q]
      linarith

    have hEq :=
      h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_positiveOverlap
        hν hNS ht hE hTail hEvolution
        q hq hBeforeQ

    have hShift :
        t + (q : ℝ) = s := by
      dsimp only [q]
      ring

    rw [hShift] at hEq

    simpa only [q] using hEq

  · unfold h3PreterminalTailCanonicalSelectedOverlapGlue
    unfold h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedOverlapGlue

    funext x

    simp only [dite_eq_right hBefore]

end
end Euclidean
end Bridge
end PrimeTensor
