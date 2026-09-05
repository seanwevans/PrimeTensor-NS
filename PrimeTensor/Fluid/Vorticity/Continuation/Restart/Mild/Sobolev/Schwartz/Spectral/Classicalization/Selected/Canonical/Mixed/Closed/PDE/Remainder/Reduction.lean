import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.Mixed.Derivative.Absolute.Time
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Mixed.Regularity.Reduction

/-!
# PDE remainder reduction after canonical selected mixed-derivative closure

The canonical selected real velocity now satisfies the mixed spacetime
`HasDerivAt` theorem in the absolute-time form used by the continuation glue.

The overlap-gluing infrastructure was built earlier against the historical
selected real-velocity wrapper.  Those two packaged velocities are exactly
equal, so this file transports the new canonical absolute-time theorem across
that equality and discharges the historical selected-side hypothesis.

Consequently the mixed field disappears from the remaining local PDE
remainder: callers supply only pressure spatial regularity and momentum.

No new estimate, derivative argument, gluing construction, or PDE identity is
introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalMixedClosedPDERemainderReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Transport the canonical absolute-time mixed derivative theorem to the
historical selected velocity wrapper used by the overlap-gluing layer. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime_of_canonical
    {nu A t0 s : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A)
    (hs :
      s ∈ Set.Ioo
        t0
        (t0 + h3FinHeatLerayRestartRadius nu A))
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun tau : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0
              (tau - t0)
              y).component j)
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun tau : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hnu U0 hA hU0
                (tau - t0)
                y).component j)
            s)
        x)
      s := by
  have hCanonical :=
    h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime
      (nu := nu)
      (A := A)
      (t0 := t0)
      (s := s)
      hnu U0 hA hU0 hs x a j

  have hVelocity :
      h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
          hnu U0 hA hU0
        =
      h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hnu U0 hA hU0 :=
    h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity_eq_mildSolutionAtRestartRadiusSelectedRealVelocity
      hnu U0 hA hU0

  rw [hVelocity] at hCanonical
  exact hCanonical

/-- The mixed regularity of the canonical local fill is closed by the canonical
absolute-time selected mixed derivative theorem. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_closed_canonical
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
      S - t < h3FinHeatLerayRestartRadius (1 : ℝ) E) :
    H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
      hNS ht hE hTail S := by
  apply
    h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_of_selected
      hNS ht hE hTail hEvolution hTS hSR

  intro s hs x i j

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime_of_canonical
      (nu := (1 : ℝ))
      (A := E)
      (t0 := t)
      (s := s)
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      hs
      x i j

/-- Direct continuation route after the canonical selected mixed derivative
field has been discharged.

The remaining supplied local PDE data are exactly pressure spatial `C²` and
momentum. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedCanonicalMixedClosedPDERemainder
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
              H3PreterminalTailUnitViscosityMomentumAt
                hNS ht hE hTail p S) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscositySelectedMixedRemainder
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

  intro s hs x i j

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime_of_canonical
      (nu := (1 : ℝ))
      (A := E)
      (t0 := t)
      (s := s)
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      hs
      x i j

end

end Euclidean
end Bridge
end PrimeTensor
