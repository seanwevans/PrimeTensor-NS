import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Time.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Unit.Viscosity.Temporal.Reduction
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Selected temporal C¹ reduced to an explicit derivative frontier

`SelectedVelocityTimeContinuity` closes zero-order time continuity of the
selected physical restart.  The remaining temporal target is therefore the
actual time derivative.

On the open absolute-time restart interval `(t,t+R)`, Mathlib's
`contDiffOn_one_iff_deriv_of_isOpen` identifies the selected `C¹` obligation
exactly with two concrete statements:

* the selected physical velocity component is differentiable in time at every
  point of the restart interval;
* its ordinary one-dimensional `deriv` is continuous on that interval.

This file packages that exact derivative frontier and threads it through the
already-reduced local PDE continuation statement.  No analytic assumption is
added: the new frontier is equivalent, through the open-set C¹ criterion, to
the selected temporal frontier from `UnitViscosityTemporalReduction`.

The next analytic rung can now target a formula for `deriv` obtained from the
positive-time mild restart identity.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Filter Set
open scoped ENNReal NNReal Interval Topology

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityTemporalDerivativeReduction
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

def H3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity
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
      let f : ℝ → ℝ :=
        fun s : ℝ =>
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
            (one_pos : (0 : ℝ) < 1)
            (h3PreterminalTailCanonicalAnchorSpectralState
              hNS ht hTail)
            (lt_of_lt_of_le zero_lt_one hE)
            (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
              hNS ht hE hTail)
            (s - t)
            x).component j
      let I : Set ℝ :=
        Set.Ioo
          t
          (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)
      DifferentiableOn ℝ f I
        ∧
      ContinuousOn (deriv f) I

theorem h3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity_iff_derivative
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E) :
    H3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity
        hNS ht hE hTail
      ↔
    H3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity
        hNS ht hE hTail := by
  constructor
  · intro hSelected
    intro x j
    dsimp only
    let f : ℝ → ℝ :=
      fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (s - t) x).component j
    let I : Set ℝ :=
      Set.Ioo t (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)
    have hC1 : ContDiffOn ℝ 1 f I := by
      simpa only [f, I] using hSelected x j
    have hCriterion :
        ContDiffOn ℝ 1 f I
          ↔
        DifferentiableOn ℝ f I ∧ ContinuousOn (deriv f) I := by
      simpa using
        (contDiffOn_succ_iff_deriv_of_isOpen
          (𝕜 := ℝ)
          (f := f)
          (s := I)
          (n := 0)
          isOpen_Ioo)

    simpa only [f, I] using hCriterion.1 hC1

  · intro hDerivative
    intro x j
    let f : ℝ → ℝ :=
      fun s : ℝ =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          (one_pos : (0 : ℝ) < 1)
          (h3PreterminalTailCanonicalAnchorSpectralState hNS ht hTail)
          (lt_of_lt_of_le zero_lt_one hE)
          (norm_h3PreterminalTailCanonicalAnchorSpectralState_le
            hNS ht hE hTail)
          (s - t) x).component j
    let I : Set ℝ :=
      Set.Ioo t (t + h3FinHeatLerayRestartRadius (1 : ℝ) E)
    have hD0 := hDerivative x j
    dsimp only at hD0
    have hD :
        DifferentiableOn ℝ f I ∧ ContinuousOn (deriv f) I := by
      simpa only [f, I] using hD0
    have hCriterion :
        ContDiffOn ℝ 1 f I
          ↔
        DifferentiableOn ℝ f I ∧ ContinuousOn (deriv f) I := by
      simpa using
        (contDiffOn_succ_iff_deriv_of_isOpen
          (𝕜 := ℝ)
          (f := f)
          (s := I)
          (n := 0)
          isOpen_Ioo)

    have hC1 : ContDiffOn ℝ 1 f I :=
      hCriterion.2 hD
    simpa only [f, I] using hC1

structure H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (S : ℝ) : Prop where

  selected_velocity_temporal_derivative :
    H3PreterminalTailUnitViscositySelectedVelocityTemporalDerivativeRegularity
      hNS ht hE hTail

  pressure_spatial_two :
    H3PreterminalTailUnitViscosityPressureSpatialRegularityAt p S

  velocity_space_time_hasDerivAt :
    H3PreterminalTailUnitViscosityVelocityMixedRegularityAt
      hNS ht hE hTail S

  momentum :
    H3PreterminalTailUnitViscosityMomentumAt hNS ht hE hTail p S

theorem h3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt_of_selectedDerivative
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t S : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (p : SpaceTimeScalarField ℝ ℝ ℝ Depth.three)
    (hFields :
      H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt
        hNS ht hE hTail p S) :
    H3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt
      hNS ht hE hTail p S := by
  refine
    {
      selected_velocity_temporal_one := ?_
      pressure_spatial_two := hFields.pressure_spatial_two
      velocity_space_time_hasDerivAt := hFields.velocity_space_time_hasDerivAt
      momentum := hFields.momentum
    }
  exact
    (h3PreterminalTailUnitViscositySelectedVelocityTemporalRegularity_iff_derivative
      hNS ht hE hTail).2
      hFields.selected_velocity_temporal_derivative

def H3PreterminalTailUnitViscositySelectedDerivativePDERemainderFrontierAt
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
        H3PreterminalTailUnitViscositySelectedDerivativePDERemainderAt
          hNS ht hE hTail p S

theorem h3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt_of_selectedDerivative
    {E : ℝ}
    {u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three}
    {T t : ℝ}
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hE : 1 ≤ E)
    (hTail : CanonicalH3TailDataFrom u t T E)
    (hDerivative :
      H3PreterminalTailUnitViscositySelectedDerivativePDERemainderFrontierAt
        hNS ht hE hTail) :
    H3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt
      hNS ht hE hTail := by
  intro hCross
  obtain ⟨p, S, hTS, hSR, hFields⟩ := hDerivative hCross
  refine ⟨p, S, hTS, hSR, ?_⟩
  exact
    h3PreterminalTailUnitViscositySelectedTemporalPDERemainderAt_of_selectedDerivative
      hNS ht hE hTail p hFields

def H3PreterminalTailUnitViscositySelectedDerivativePDERemainderFrontier : Prop :=
  ∀
    (E : ℝ)
    (hE : 1 ≤ E)
    (u : SpaceTimeVectorField ℝ ℝ MulReal Depth.three)
    (T t : ℝ)
    (hNS : LoggedPreterminalNavierStokesAdmissible u T)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hTail : CanonicalH3TailDataFrom u t T E),
      H3PreterminalTailUnitViscositySelectedDerivativePDERemainderFrontierAt
        hNS ht hE hTail

theorem h3ControlProducesExtension_of_unitViscositySelectedDerivativePDERemainder
    (hEvolution :
      H3PreterminalTailPhysicalEvolutionFrontier
        (1 : ℝ)
        (one_pos : (0 : ℝ) < 1))
    (hRemainder :
      H3PreterminalTailUnitViscositySelectedDerivativePDERemainderFrontier) :
    H3ControlProducesExtension := by
  apply
    h3ControlProducesExtension_of_unitViscositySelectedTemporalPDERemainder
      hEvolution
  intro E hE u T t hNS ht hTail
  exact
    h3PreterminalTailUnitViscositySelectedTemporalPDERemainderFrontierAt_of_selectedDerivative
      hNS ht hE hTail
      (hRemainder E hE u T t hNS ht hTail)

end
end Euclidean
end Bridge
end PrimeTensor
