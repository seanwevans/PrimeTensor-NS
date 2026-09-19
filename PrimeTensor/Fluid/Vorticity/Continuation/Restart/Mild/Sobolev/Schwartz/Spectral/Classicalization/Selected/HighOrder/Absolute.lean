import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Spatial.Five
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.Selected.C4
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Pressure.Absolute.Time

/-!
# Selected high-order regularity in absolute preterminal time

The selected restart now exposes both pieces required by the high-order energy
class:

* velocity spatial `C⁵`;
* pressure spatial `C⁴`.

Those theorems are naturally stated in elapsed restart time `r`.  The overlap
and old-solution layers work in absolute time `s`, with

    r = s - t.

This file performs that clock conversion once.

For every absolute time in the strict selected window

    t < s < t + R,

we obtain exactly the local regularity shapes used later by
`PreterminalH3EnergyClass`:

    ∂ᵢ∂ₖ uⱼ(s) ∈ C³,
    ∂ᵢ p_sel(s) ∈ C³.

No new Fourier estimate, PDE estimate, or uniqueness argument appears here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedAbsoluteHighOrder
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-! ## Common elapsed-time bookkeeping -/

/-- Absolute strict selected-window membership gives positive elapsed time. -/
private theorem selectedAbsolute_elapsed_pos
    {t s R : ℝ}
    (hs : s ∈ Set.Ioo t (t + R)) :
    0 < s - t :=
  sub_pos.mpr hs.1

/-- Absolute strict selected-window membership gives elapsed time at most the
restart radius. -/
private theorem selectedAbsolute_elapsed_le
    {t s R : ℝ}
    (hs : s ∈ Set.Ioo t (t + R)) :
    s - t ≤ R := by
  have hlt : s - t < R := by
    exact
      (sub_lt_iff_lt_add).2
        (by simpa only [add_comm] using hs.2)
  exact hlt.le

/-! ## Velocity C5 in absolute time -/

/--
At every absolute time in the strict selected restart window, each intrinsic
selected velocity component is spatially `C⁵`.
-/
theorem h3PreterminalTailCanonicalSelectedVelocityAbsolute_contDiff_five
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail
    ContDiff ℝ 5
      (fun y =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          U₀
          hA
          hU₀
          (s - t)
          y).component j) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  have hs0 :
      0 < s - t :=
    selectedAbsolute_elapsed_pos hs

  have hsR :
      s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    selectedAbsolute_elapsed_le hs

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_contDiff_fiveAt
      (one_pos : (0 : ℝ) < 1)
      U₀
      hA
      hU₀
      hs0
      hsR
      j

/--
Exact absolute-time `VelocitySpatialC5OnTail` local shape for the selected
restart.
-/
theorem h3PreterminalTailCanonicalSelectedVelocityAbsolute_secondPartial_spatialC3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (j i k : PrimeTensor.Axis Depth.three) :
    let U₀ : H3SpectralVelocityState :=
      h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail
    let hA : 0 < E :=
      lt_of_lt_of_le zero_lt_one hE
    let hU₀ : ‖U₀‖ ≤ E :=
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail
    SpatialC3
      (spatial3.d i
        (spatial3.d k
          (fun y =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              (one_pos : (0 : ℝ) < 1)
              U₀
              hA
              hU₀
              (s - t)
              y).component j))) := by
  dsimp only

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  have hs0 :
      0 < s - t :=
    selectedAbsolute_elapsed_pos hs

  have hsR :
      s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    selectedAbsolute_elapsed_le hs

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_secondPartial_spatialC3At
      (one_pos : (0 : ℝ) < 1)
      U₀
      hA
      hU₀
      hs0
      hsR
      j i k

/-! ## Pressure C4 in absolute time -/

/--
The canonical selected pressure is spatially `C⁴` throughout the strict
absolute selected restart window.
-/
theorem h3PreterminalTailCanonicalSelectedPressureAbsolute_contDiff_four
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    ContDiff ℝ 4
      (h3PreterminalTailCanonicalSelectedPressureAbsolute
        hNS ht hE hTail s) := by

  let U₀ : H3SpectralVelocityState :=
    h3PreterminalTailCanonicalAnchorSpectralState
      hNS ht hTail

  have hA : 0 < E :=
    lt_of_lt_of_le zero_lt_one hE

  have hU₀ : ‖U₀‖ ≤ E := by
    dsimp only [U₀]
    exact
      norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail

  have hs0 :
      0 < s - t :=
    selectedAbsolute_elapsed_pos hs

  have hsR :
      s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E :=
    selectedAbsolute_elapsed_le hs

  have hSelected :=
    h3RawFinPressureRealC1OfPath_selectedRestart_contDiff_four
      (one_pos : (0 : ℝ) < 1)
      U₀
      hA
      hU₀
      hs0
      hsR

  simpa only [
    U₀,
    h3PreterminalTailCanonicalSelectedPressureAbsolute,
    h3PreterminalTailCanonicalSelectedRestart
  ] using hSelected

/--
Exact absolute-time `PressureSpatialC4OnTail` local shape for the selected
pressure.
-/
theorem h3PreterminalTailCanonicalSelectedPressureAbsolute_spatialDerivative_spatialC3
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t s : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))
    (i : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (spatial3.d i
        (h3PreterminalTailCanonicalSelectedPressureAbsolute
          hNS ht hE hTail s)) := by

  let p : ScalarField3 :=
    h3PreterminalTailCanonicalSelectedPressureAbsolute
      hNS ht hE hTail s

  have hp4 :
      ContDiff ℝ 4 p := by
    dsimp only [p]
    exact
      h3PreterminalTailCanonicalSelectedPressureAbsolute_contDiff_four
        hNS ht hE hTail hs

  have hp3 :
      SpatialC3 p := by
    unfold SpatialC3
    exact hp4.of_le (by norm_num)

  change
    SpatialC3
      (fun x : Point3 =>
        partialDeriv i p x)

  rw [
    PrimeTensor.Bridge.Euclidean.SpatialC3.partialDeriv_fun_eq
      hp3 i
  ]

  unfold SpatialC3

  exact
    (hp4.fderiv_right (by norm_num)).clm_apply
      contDiff_const

end

end Euclidean
end Bridge
end PrimeTensor
