import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Third.Jet.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SpatialRegularity

/-!
# Classicalization: selected real velocity spatial regularity

The selected restart velocity is already packaged as an ordinary PrimeTensor
real velocity field in `SelectedVelocityThirdJetContinuity`.

This file records the spatial half of the classicalization package at the
velocity level.

For every strictly positive restart time `s` up to and including the canonical
restart radius, every intrinsic velocity component is spatially `C³`.  The
proof is only representation transport:

* convert the intrinsic `Axis Depth.three` component to the corresponding
  spectral `Fin 3` coordinate;
* use the already-compiled arbitrary-order inverse-Fourier regularity theorem;
* specialize that theorem to order three.

The radius endpoint is included because the moment/spatial-regularity theorem
is available under `s ≤ R`, unlike the third-jet time-continuity statement,
which naturally lives on the open interval.

No claim is made at restart time zero for an arbitrary spectral initial state.
That slice will be supplied later from the preterminal classical snapshot in
the canonical restart/gluing layer.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open Set
open scoped Topology

noncomputable section

noncomputable local instance axisFintypeH3SchwartzClassicalizationSelectedVelocitySpatialRegularity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  axisFintypeH3SchwartzFrechetInductionMomentAlgebra d

/-- Every intrinsic component of the selected reconstructed real velocity is
spatially `C³` at a strictly positive restart time up to the canonical restart
radius. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
    {ν A s : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hs : 0 < s)
    (hsR : s ≤ h3FinHeatLerayRestartRadius ν A)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (fun y =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀ s y).component j) := by
  change
    SpatialC3
      (h3SpectralVelocityRealC1RepresentativeOnPoint3
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀ s)
        (h3ClassicalizationFinOfAxis j))

  unfold SpatialC3

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_velocityRealC1RepresentativeOnPoint3_contDiff_three
      hν U₀ hA hU₀ hs hsR
      (h3ClassicalizationFinOfAxis j)

/-- Velocity-level spatial `C³` regularity on the positive half-open restart
window `(0,R]`. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3On_Ioc
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A) :
    ∀ s : ℝ,
      s ∈ Set.Ioc
        (0 : ℝ)
        (h3FinHeatLerayRestartRadius ν A) →
      ∀ j : PrimeTensor.Axis Depth.three,
        SpatialC3
          (fun y =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ s y).component j) := by
  intro s hs j

  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
      hν U₀ hA hU₀
      hs.1 hs.2
      j

/-- In particular, the selected reconstructed velocity is spatially `C³` at
the canonical restart-radius endpoint itself. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At_radius
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (j : PrimeTensor.Axis Depth.three) :
    SpatialC3
      (fun y =>
        (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
          hν U₀ hA hU₀
          (h3FinHeatLerayRestartRadius ν A)
          y).component j) := by
  exact
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_spatialC3At
      hν U₀ hA hU₀
      (h3FinHeatLerayRestartRadius_pos ν hA)
      le_rfl
      j

end
end Euclidean
end Bridge
end PrimeTensor
