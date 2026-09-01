import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedTemporalClosedPDERemainderReduction

/-!
# Selected velocity mixed regularity reduction

After the selected temporal derivative frontier has been closed, the remaining
mixed spacetime obligation should not contain an independent gluing problem.

The canonical local fill has two exact classical descriptions on open time
neighborhoods:

* before the old terminal time `T`, it is the original logged preterminal
  Navier--Stokes velocity, whose regularity package already contains the
  required mixed `HasDerivAt`;
* throughout the positive selected restart window, physical-tail evolution
  identifies it with the selected real restart.

This file transports the mixed derivative through those local equalities.  The
selected-side assumption is deliberately written in absolute time,

    τ ↦ selectedVelocity (τ - t),

so no additional chain-rule argument is needed.  Local equality transports both
the time derivative of the spatial partial and the spatial partial of the time
derivative using `HasDerivAt.congr_of_eventuallyEq` and
`Filter.EventuallyEq.deriv_eq`.

No new named frontier proposition and no new analytic estimate are introduced.
The continuation theorem at the end simply replaces the glued mixed field by
the genuine selected-side mixed derivative statement.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityMixedRegularityReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- A mixed derivative statement for the selected restart in absolute time
propagates through the old/selected overlap glue to the canonical local fill. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_of_selected
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
      ∀
        (s : ℝ),
          s ∈
              Set.Ioo
                t
                (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) →
          ∀
            (x : Point3)
            (i j : PrimeTensor.Axis Depth.three),
              HasDerivAt
                (fun τ : ℝ =>
                  spatial3.d
                    i
                    (fun y =>
                      (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                        (one_pos : (0 : ℝ) < 1)
                        (h3PreterminalTailCanonicalAnchorSpectralState
                          hNS ht hTail)
                        (lt_of_lt_of_le zero_lt_one hE)
                        (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                          hNS ht hE hTail)
                        (τ - t)
                        y).component j)
                    x)
                (spatial3.d
                  i
                  (fun y =>
                    temporal.d
                      (fun τ : ℝ =>
                        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                          (one_pos : (0 : ℝ) < 1)
                          (h3PreterminalTailCanonicalAnchorSpectralState
                            hNS ht hTail)
                          (lt_of_lt_of_le zero_lt_one hE)
                          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                            hNS ht hE hTail)
                          (τ - t)
                          y).component j)
                      s)
                  x)
                s) :
    H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
      hNS ht hE hTail S := by
  unfold H3PreterminalTailUnitViscosityVelocityMixedRegularityAt

  intro s hs x i j

  let p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three :=
    Classical.choose hNS

  have hPDE :
      PreterminalNavierStokes3
        (logSpaceTimeVectorField u)
        p
        T :=
    Classical.choose_spec hNS

  by_cases hBefore : s < T

  · have hsOld : s ∈ Set.Ioo (0 : ℝ) T :=
      ⟨hs.1, hBefore⟩

    have hOld :=
      hPDE.regularity.velocity_space_time_hasDerivAt
        s hsOld x i j

    have hNeighborhood :
        Set.Ioo (0 : ℝ) T ∈ 𝓝 s :=
      Ioo_mem_nhds hs.1 hBefore

    have hScalarEq
        (r : ℝ)
        (hr : r ∈ Set.Ioo (0 : ℝ) T) :
        (fun y : Point3 =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j)
          =
        (fun y : Point3 =>
          (logSpaceTimeVectorField u r y).component j) := by
      have hrS : r ∈ Set.Ioo (0 : ℝ) S :=
        ⟨hr.1, lt_trans hr.2 hTS⟩

      have hAgree :
          logSpaceTimeVectorField u r
            =
          h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail r :=
        h3PreterminalTailCanonicalSelectedOverlapGlue_agreesBeforeT
          (one_pos : (0 : ℝ) < 1)
          hNS ht hE hTail
          r hr

      funext y

      calc
        (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j
            =
          (h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail r y).component j := by
              rw [
                h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_eq_glue_of_mem
                  hNS ht hE hTail hrS
              ]
        _ =
          (logSpaceTimeVectorField u r y).component j := by
            rw [← hAgree]

    have hSpatialEq :
        (fun r : ℝ =>
          spatial3.d
            i
            (fun y =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            x)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          spatial3.d
            i
            (fun y =>
              (logSpaceTimeVectorField u r y).component j)
            x) := by
      filter_upwards [hNeighborhood] with r hr
      exact
        congrArg
          (fun f : ScalarField3 => spatial3.d i f x)
          (hScalarEq r hr)

    have hTimeEq (y : Point3) :
        (fun r : ℝ =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          (logSpaceTimeVectorField u r y).component j) := by
      filter_upwards [hNeighborhood] with r hr
      exact congrFun (hScalarEq r hr) y

    have hTemporalFieldEq :
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            s)
          =
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (logSpaceTimeVectorField u r y).component j)
            s) := by
      funext y
      change
        deriv
            (fun r : ℝ =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            s
          =
        deriv
            (fun r : ℝ =>
              (logSpaceTimeVectorField u r y).component j)
            s
      exact (hTimeEq y).deriv_eq

    have hCoefficientEq :
        spatial3.d
            i
            (fun y =>
              temporal.d
                (fun r : ℝ =>
                  (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                    hNS ht hE hTail S r y).component j)
                s)
            x
          =
        spatial3.d
            i
            (fun y =>
              temporal.d
                (fun r : ℝ =>
                  (logSpaceTimeVectorField u r y).component j)
                s)
            x :=
      congrArg
        (fun f : ScalarField3 => spatial3.d i f x)
        hTemporalFieldEq

    rw [hCoefficientEq]

    exact
      hOld.congr_of_eventuallyEq hSpatialEq

  · have hsT : T ≤ s :=
      le_of_not_gt hBefore

    have hts : t < s :=
      lt_of_lt_of_le ht.2 hsT

    have hSUpper :
        S < t + h3FinHeatLerayRestartRadius (1 : ℝ) E := by
      linarith

    have hsSelected :
        s ∈
          Set.Ioo
            t
            (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) :=
      ⟨hts, lt_trans hs.2 hSUpper⟩

    have hSelectedAt :=
      hSelected s hsSelected x i j

    have hNeighborhood :
        Set.Ioo t S ∈ 𝓝 s :=
      Ioo_mem_nhds hts hs.2

    have hScalarEq
        (r : ℝ)
        (hr : r ∈ Set.Ioo t S) :
        (fun y : Point3 =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j)
          =
        (fun y : Point3 =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (r - t)
            y).component j) := by
      have hrS : r ∈ Set.Ioo (0 : ℝ) S :=
        ⟨lt_trans ht.1 hr.1, hr.2⟩

      have hrR :
          r - t ≤ h3FinHeatLerayRestartRadius (1 : ℝ) E := by
        have hlt :
            r - t < h3FinHeatLerayRestartRadius (1 : ℝ) E := by
          linarith [hr.2, hSR]
        exact hlt.le

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
          r hr.1 hrR

      funext y

      calc
        (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j
            =
          (h3PreterminalTailCanonicalSelectedOverlapGlue
            (one_pos : (0 : ℝ) < 1)
            hNS ht hE hTail r y).component j := by
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
            y).component j := by
              rw [hEq]

    have hSpatialEq :
        (fun r : ℝ =>
          spatial3.d
            i
            (fun y =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            x)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          spatial3.d
            i
            (fun y =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalTailCanonicalAnchorSpectralState
                  hNS ht hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                  hNS ht hE hTail)
                (r - t)
                y).component j)
            x) := by
      filter_upwards [hNeighborhood] with r hr
      exact
        congrArg
          (fun f : ScalarField3 => spatial3.d i f x)
          (hScalarEq r hr)

    have hTimeEq (y : Point3) :
        (fun r : ℝ =>
          (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
            hNS ht hE hTail S r y).component j)
          =ᶠ[𝓝 s]
        (fun r : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (r - t)
            y).component j) := by
      filter_upwards [hNeighborhood] with r hr
      exact congrFun (hScalarEq r hr) y

    have hTemporalFieldEq :
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            s)
          =
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalTailCanonicalAnchorSpectralState
                  hNS ht hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                  hNS ht hE hTail)
                (r - t)
                y).component j)
            s) := by
      funext y
      change
        deriv
            (fun r : ℝ =>
              (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                hNS ht hE hTail S r y).component j)
            s
          =
        deriv
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                (one_pos : (0 : ℝ) < 1)
                (h3PreterminalTailCanonicalAnchorSpectralState
                  hNS ht hTail)
                (lt_of_lt_of_le zero_lt_one hE)
                (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                  hNS ht hE hTail)
                (r - t)
                y).component j)
            s
      exact (hTimeEq y).deriv_eq

    have hCoefficientEq :
        spatial3.d
            i
            (fun y =>
              temporal.d
                (fun r : ℝ =>
                  (h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill
                    hNS ht hE hTail S r y).component j)
                s)
            x
          =
        spatial3.d
            i
            (fun y =>
              temporal.d
                (fun r : ℝ =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    (one_pos : (0 : ℝ) < 1)
                    (h3PreterminalTailCanonicalAnchorSpectralState
                      hNS ht hTail)
                    (lt_of_lt_of_le zero_lt_one hE)
                    (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                      hNS ht hE hTail)
                    (r - t)
                    y).component j)
                s)
            x :=
      congrArg
        (fun f : ScalarField3 => spatial3.d i f x)
        hTemporalFieldEq

    rw [hCoefficientEq]

    exact
      hSelectedAt.congr_of_eventuallyEq hSpatialEq

/-- Direct continuation route with the mixed spacetime obligation moved from
the glued local fill to the selected restart itself.

As in the preceding temporal-closure reduction, no new named frontier `Prop` is
introduced.  Pressure `C²` and momentum remain unchanged; only the mixed field
is replaced by its genuine selected-side analytic statement. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedMixedRemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hRemainder :
      ∀
        (E : ℝ)
        (hE : 1 ≤ E)
        (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
        (T t : ℝ)
        (hNS : LoggedPreterminalNavierStokesAdmissible u T)
        (ht : t ∈ Set.Ioo (0 : ℝ) T)
        (hTail : CanonicalH3TailDataFrom u t T E),
          T - t < h3FinHeatLerayRestartRadius (1 : ℝ) E →
          ∃
            (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
            (S : ℝ),
              T < S
                ∧
              S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E
                ∧
              H3PreterminalTailUnitViscosityPressureSpatialRegularityAt
                p S
                ∧
              (∀
                (s : ℝ),
                  s ∈
                      Set.Ioo
                        t
                        (t + h3FinHeatLerayRestartRadius (1 : ℝ) E) →
                  ∀
                    (x : Point3)
                    (i j : PrimeTensor.Axis Depth.three),
                      HasDerivAt
                        (fun τ : ℝ =>
                          spatial3.d
                            i
                            (fun y =>
                              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                (one_pos : (0 : ℝ) < 1)
                                (h3PreterminalTailCanonicalAnchorSpectralState
                                  hNS ht hTail)
                                (lt_of_lt_of_le zero_lt_one hE)
                                (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                                  hNS ht hE hTail)
                                (τ - t)
                                y).component j)
                            x)
                        (spatial3.d
                          i
                          (fun y =>
                            temporal.d
                              (fun τ : ℝ =>
                                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                                  (one_pos : (0 : ℝ) < 1)
                                  (h3PreterminalTailCanonicalAnchorSpectralState
                                    hNS ht hTail)
                                  (lt_of_lt_of_le zero_lt_one hE)
                                  (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
                                    hNS ht hE hTail)
                                  (τ - t)
                                  y).component j)
                              s)
                          x)
                        s)
                ∧
              H3PreterminalTailUnitViscosityMomentumAt
                hNS ht hE hTail p S) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscositySelectedTemporalClosedPDERemainder
      hEvolution

  intro E hE u T t hNS ht hTail
  intro hCross

  obtain
    ⟨
      p,
      S,
      hTS,
      hSR,
      hPressure,
      hSelectedMixed,
      hMomentum
    ⟩ :=
      hRemainder E hE u T t hNS ht hTail hCross

  refine
    ⟨
      p,
      S,
      hTS,
      hSR,
      hPressure,
      ?_,
      hMomentum
    ⟩

  exact
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_of_selected
      hNS ht hE hTail
      (hEvolution E hE u T t hNS ht hTail)
      hTS hSR
      hSelectedMixed

end

end Euclidean
end Bridge
end PrimeTensor
