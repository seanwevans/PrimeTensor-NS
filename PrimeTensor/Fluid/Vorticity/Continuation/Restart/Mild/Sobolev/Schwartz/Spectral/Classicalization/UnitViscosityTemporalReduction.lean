import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.UnitViscosityPDEReduction
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.PhysicalTailClassicalOverlap

/-!
# Unit-viscosity temporal regularity reduced to the selected restart

After incompressibility, the reduced local PDE frontier still asks directly for
componentwise temporal `C¹` regularity of the total local-fill field.

That packaging obscures where the remaining analysis actually lives.  The
canonical glue has two exact classical descriptions on overlapping open
regions:

* before `T`, it is the original logged preterminal Navier--Stokes velocity;
* throughout the positive selected restart window `(t,t+R)`, physical-tail
  evolution identifies it exactly with the selected real restart.

Since `t < T`, these two regions overlap.  Consequently there is no independent
time-derivative matching problem at the branch cut `T`: local `C¹` regularity
glues through the overlap automatically.

This file isolates the genuine remaining temporal target as `C¹` regularity of
the absolute-time selected restart on `(t,t+R)`, then proves that target implies
the previous local-fill temporal-regularity field.  The continuation frontier
is repackaged accordingly.

No new analytic assumption is added; the old local-fill `C¹` obligation is
strictly reduced to the selected positive-time evolution.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3UnitViscosityTemporalReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The genuine selected-side temporal regularity target.

Time is written in absolute coordinates so that the selected restart appears
as `s - t` on the open window `(t,t+R)`. -/
def H3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) : Prop :=
  ∀
    (x : Point3)
    (j : PrimeTensor.Axis Depth.three),
      ContDiffOn
        ℝ 1
        (fun s : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (s - t)
            x).component j)
        (Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E))

/-- Selected temporal `C¹` regularity propagates through the canonical overlap
glue and the local-fill wrapper.

The proof is local on `(0,S)`.  At a point before `T` we use the original
preterminal `C¹` regularity on the open neighborhood `Iio T`.  At a point at or
after `T`, the inequality `t < T ≤ s` places us inside `Ioi t`, where physical
tail evolution identifies the glue with the selected restart.  The endpoint
bound `S - t < R` keeps that entire local piece inside the selected radius. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityTemporalRegularity_of_selected
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
    (hSelected :
      H3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityVelocityTemporalRegularityAt
      hNS ht hE hTail S := by
  intro x j

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
      ContDiffOn
        ℝ 1
        (fun s : ℝ =>
          (logSpaceTimeVectorField u s x).component j)
        (Set.Ioo (0 : ℝ) T) :=
    hPDE.regularity.velocity_temporal_one x j

  have hSelectedC1 :
      ContDiffOn
        ℝ 1
        (fun s : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (s - t)
            x).component j)
        (Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)) :=
    hSelected x j

  apply contDiffOn_of_locally_contDiffOn
  intro s hs

  by_cases hBefore : s < T

  · refine
      ⟨
        Set.Iio T,
        isOpen_Iio,
        hBefore,
        ?_
      ⟩

    have hSub :
        Set.Ioo (0 : ℝ) S ∩ Set.Iio T
          ⊆
        Set.Ioo (0 : ℝ) T := by
      intro r hr
      exact ⟨hr.1.1, hr.2⟩

    apply (hOld.mono hSub).congr
    intro r hr

    have hrS :
        r ∈ Set.Ioo (0 : ℝ) S :=
      hr.1

    have hrT :
        r ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hrS.1, hr.2⟩

    have hAgree :
        logSpaceTimeVectorField u r
          =
        h3PreterminalTailCanonicalSelectedOverlapGlue
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail r :=
      h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail
        r hrT

    calc
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
          hNS ht hE hTail S r x).component j
          =
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail r x).component j := by
            rw [
              h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
                hNS ht hE hTail hrS
            ]
      _ =
        (logSpaceTimeVectorField u r x).component j := by
          rw [← hAgree]

  · have hsT : T ≤ s :=
      le_of_not_gt hBefore

    have hts : t < s :=
      lt_of_lt_of_le ht.2 hsT

    refine
      ⟨
        Set.Ioi t,
        isOpen_Ioi,
        hts,
        ?_
      ⟩

    have hSUpper :
        S < t + h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      linarith

    have hSub :
        Set.Ioo (0 : ℝ) S ∩ Set.Ioi t
          ⊆
        Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) := by
      intro r hr
      exact
        ⟨
          hr.2,
          lt_trans hr.1.2 hSUpper
        ⟩

    apply (hSelectedC1.mono hSub).congr
    intro r hr

    have hrS :
        r ∈ Set.Ioo (0 : ℝ) S :=
      hr.1

    have htr : t < r :=
      hr.2

    have hrR :
        r - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      have :
          r - t < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        linarith [hrS.2, hSR]
      exact this.le

    have hEq :
        h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail r
          =
        h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (r - t) :=
      h3PreterminalTailCanonicalSelectedOverlapGlue_eq_selected_on_restartWindow
        (one_pos : (0 : ℝ) < 1)
        hNS ht hE hTail hEvolution
        r htr hrR

    calc
      (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
          hNS ht hE hTail S r x).component j
          =
        (h3PreterminalTailCanonicalSelectedOverlapGlue
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail r x).component j := by
            rw [
              h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
                hNS ht hE hTail hrS
            ]
      _ =
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState
            hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (r - t)
          x).component j := by
            rw [hEq]

/-- Four-field PDE remainder with temporal regularity stated only on the
selected restart, rather than on the already-glued local field. -/
structure H3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ) : Prop where

  selected_velocity_temporal_one :
    H3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity
      hNS ht hE hTail

  pressure_spatial_two :
    H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
      p S

  velocity_space_time_hasDerivAt :
    H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
      hNS ht hE hTail S

  momentum :
    H3PreterminalTailUnitViscosityMomentumAt
      hNS ht hE hTail p S

/-- Convert the selected-temporal remainder into the previous local-fill
remainder using physical overlap and the radius bound. -/
theorem h3PreterminalTailUnitViscosityLocalPDERemainderAt_of_selectedTemporal
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
    (hFields :
      H3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt
        hNS ht hE hTail p S) :
    H3PreterminalTailUnitViscosityLocalPDERemainderAt
      hNS ht hE hTail p S := by
  refine
    {
      velocity_temporal_one := ?_
      pressure_spatial_two :=
        hFields.pressure_spatial_two
      velocity_space_time_hasDerivAt :=
        hFields.velocity_space_time_hasDerivAt
      momentum :=
        hFields.momentum
    }

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityTemporalRegularity_of_selected
      hNS ht hE hTail
      hEvolution hTS hSR
      hFields.selected_velocity_temporal_one

/-- Reduced local frontier in which temporal `C¹` is a selected-restart
property rather than a gluing property. -/
def H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt
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
        H3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt
          hNS ht hE hTail p S

/-- The selected-temporal frontier implies the previous four-field local PDE
remainder frontier once physical-tail evolution is available. -/
theorem h3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt_of_selectedTemporal
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
    (hSelected :
      H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt
      hNS ht hE hTail := by
  intro hCross

  obtain
    ⟨p, S, hTS, hSR, hFields⟩ :=
      hSelected hCross

  refine
    ⟨
      p,
      S,
      hTS,
      hSR,
      ?_
    ⟩

  exact
    h3PreterminalTailUnitViscosityLocalPDERemainderAt_of_selectedTemporal
      hNS ht hE hTail
      hEvolution hTS hSR
      p hFields

/-- Global selected-temporal local-PDE frontier. -/
def H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt
        hNS ht hE hTail

/-- The continuation theorem after pushing temporal `C¹` entirely onto the
selected restart. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedTemporalPDERemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hRemainder :
      H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontier) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscosityPDERemainder
      hEvolution

  intro E hE u T t hNS ht hTail

  exact
    h3PreterminalTailUnitViscosityLocalPDERemainderFrontierAt_of_selectedTemporal
      hNS ht hE hTail
      (hEvolution E hE u T t hNS ht hTail)
      (hRemainder E hE u T t hNS ht hTail)

end
end Euclidean
end Bridge
end PrimeTensor
