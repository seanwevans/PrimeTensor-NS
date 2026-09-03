import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Nonlinear.Forcing.Pressure.SelectedC2
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureMomentum

/-!
# Selected H³ pressure in absolute continuation time

The pressure constructed from the selected mild restart is naturally
parameterized by elapsed restart time `r`.  The continuation glue instead uses
absolute time `s`, with

    r = s - t.

This file performs that bookkeeping once and for all.

For the canonical preterminal anchor at time `t`, define the absolute selected
pressure by

    p_sel(s,x) = p_restart(s - t,x).

At every absolute time in the strict selected restart window

    t < s < t + R,

the elapsed time satisfies

    0 < s - t < R.

Therefore the selected `SpatialC2` theorem from `Pressure.SelectedC2` applies
directly.

No new estimate or regularity argument is introduced here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureAbsoluteTime
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical selected pressure written in the absolute time coordinate used by
the continuation glue. -/
noncomputable def h3PreterminalTailCanonicalSelectedPressureAbsolute
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  let W : ℝ → H3SpectralFinVectorState :=
    h3PreterminalTailCanonicalSelectedRestart
      (one_pos : (0 : ℝ) < 1)
      hNS ht hE hTail
  fun s =>
    h3RawFinPressureRealC1OfPath W (s - t)

/-- The absolute selected pressure is spatially `C²` throughout the strict
positive selected restart window. -/
theorem h3PreterminalTailCanonicalSelectedPressureAbsolute_spatialC2
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    {s : ℝ}
    (hs :
      s ∈ Set.Ioo
        t
        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)) :
    SpatialC2
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

  have hs0 : 0 < s - t :=
    sub_pos.mpr hs.1

  have hsR :
      s - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
    have hlt :
        s - t < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      exact
        (sub_lt_iff_lt_add).2
          (by simpa only [add_comm] using hs.2)
    exact hlt.le

  have hSelected :=
    h3RawFinPressureRealC1OfPath_selectedRestart_spatialC2
      (one_pos : (0 : ℝ) < 1)
      U₀ hA hU₀ hs0 hsR

  simpa only [
    U₀,
    h3PreterminalTailCanonicalSelectedPressureAbsolute,
    h3PreterminalTailCanonicalSelectedRestart
  ] using hSelected

end

end Euclidean
end Bridge
end PrimeTensor
