import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedPressureAbsoluteTime
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.UnitViscosityPDEDecomposition

/-!
# Pressure splice for the canonical H³ local fill

The velocity local fill already uses the old preterminal solution before `T`
and the selected restart after the overlap branch point.  The pressure now has
matching classical representatives on the two corresponding regions:

* before `T`, use the pressure carried by the logged
  `PreterminalNavierStokes3` witness;
* at and after `T`, use the canonical selected inverse-Fourier pressure in
  absolute time.

Pressure regularity in the continuation remainder is purely spatial and
slice-by-slice, so no time-gluing regularity is required.  On any endpoint
`S` lying strictly inside the selected restart window, this piecewise pressure
is spatially `C²` throughout `(0,S)`.

The branch at `T` is deliberately assigned to the selected pressure.  The
crossing hypothesis places `T` strictly after the restart anchor `t` and
strictly before the selected restart endpoint, so the selected positive-time
`C²` theorem applies there.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedPressureLocalFill
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Piecewise physical pressure paired with the canonical old/selected local
velocity fill. -/
noncomputable def h3PreterminalTailCanonicalSelectedPressureLocalFill
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS
  fun s =>
    if hs : s < T then
      pOld s
    else
      h3PreterminalTailCanonicalSelectedPressureAbsolute
        hNS ht hE hTail s

/-- On every local endpoint strictly inside the selected restart window, the
piecewise pressure has the exact spatial `C²` regularity required by the
unit-viscosity continuation remainder. -/
theorem h3PreterminalTailCanonicalSelectedPressureLocalFill_pressureSpatialRegularity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hTS : T < S)
    (hSR :
      S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
      (h3PreterminalTailCanonicalSelectedPressureLocalFill
        hNS ht hE hTail)
      S := by
  intro s hs

  let pOld : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        pOld
        T := by
    dsimp only [pOld]
    exact Classical.choose_spec hNS

  by_cases hBefore : s < T

  · have hsOld : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, hBefore⟩

    have hOld :
        SpatialC2 (pOld s) :=
      hPDE.regularity.pressure_spatial_two
        s hsOld

    simpa only [
      h3PreterminalTailCanonicalSelectedPressureLocalFill,
      pOld,
      dif_pos hBefore
    ] using hOld

  · have hsT : T ≤ s :=
      le_of_not_gt hBefore

    have hts : t < s :=
      lt_of_lt_of_le ht.2 hsT

    have hSUpper :
        S < t + h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      linarith [hSR]

    have hsSelected :
        s ∈ Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨hts, lt_trans hs.2 hSUpper⟩

    have hSelected :
        SpatialC2
          (h3PreterminalTailCanonicalSelectedPressureAbsolute
            hNS ht hE hTail s) :=
      h3PreterminalTailCanonicalSelectedPressureAbsolute_spatialC2
        hNS ht hE hTail hsSelected

    simpa only [
      h3PreterminalTailCanonicalSelectedPressureLocalFill,
      pOld,
      dif_neg hBefore
    ] using hSelected

end

end Euclidean
end Bridge
end PrimeTensor
