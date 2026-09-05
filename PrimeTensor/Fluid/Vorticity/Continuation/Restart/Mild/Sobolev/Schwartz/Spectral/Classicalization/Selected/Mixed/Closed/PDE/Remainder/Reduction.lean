import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Mixed.Derivative.Absolute.Time
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Mixed.Regularity.Reduction

/-!
# PDE remainder reduction after selected mixed-derivative closure

The selected mixed spacetime derivative is now a theorem of the canonical
restart construction, including the absolute-time translation used by the
continuation glue:

    τ ↦ selectedVelocity (τ - t).

Therefore callers should no longer be asked to supply the selected mixed
`HasDerivAt` field as part of the local PDE remainder.

This file mirrors the earlier temporal-closure reduction:

* a local constructor inserts the proved absolute-time selected mixed
  derivative into the overlap-glue regularity theorem;
* a direct continuation theorem reduces the supplied local PDE remainder from
  pressure + mixed derivative + momentum to pressure + momentum.

No new named frontier proposition and no new analytic estimate are introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedMixedClosedPDERemainderReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The mixed regularity of the canonical local fill is now closed: its
selected-side hypothesis is supplied by the proved absolute-time selected
mixed derivative theorem. -/
theorem h3PreterminalTailCanonicalSelectedOverlapGlueLocalFill_velocityMixedRegularity_closed
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
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime
      (ν := (1 : ℝ))
      (A := E)
      (t₀ := t)
      (s := s)
      (one_pos : (0 : ℝ) < 1)
      (h3PreterminalTailCanonicalAnchorSpectralState
        hNS ht hTail)
      (lt_of_lt_of_le zero_lt_one hE)
      (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
        hNS ht hE hTail)
      hs
      x i j

/-- Direct continuation route after the selected mixed derivative field has
been discharged.

The remaining supplied local PDE data are exactly pressure spatial `C²` and
momentum. -/
theorem h3ControlProducesExtension_of_unitViscositySelectedMixedClosedPDERemainder
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
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_absoluteTime
      (ν := (1 : ℝ))
      (A := E)
      (t₀ := t)
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
