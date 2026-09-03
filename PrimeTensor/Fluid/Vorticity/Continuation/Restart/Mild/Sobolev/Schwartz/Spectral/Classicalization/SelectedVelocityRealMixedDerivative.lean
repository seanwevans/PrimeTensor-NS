import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.SelectedVelocityRealSpatialPartialTimeDerivative

/-!
# Classicalization: selected real velocity mixed derivative

The preceding scalar-coordinate theorem proves the actual mixed derivative on
the real `Point3` representative:

    d/dt (∂ₐ uᵢ) = ∂ₐ (d/dt uᵢ).

This file packages that theorem in the project's selected real velocity
language.  The only additional work is the exact conversion between a concrete
`Axis Depth.three` component and its `Fin 3` spectral coordinate.

No new estimate, derivative calculation, or mixed-partial argument is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealMixedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- The intrinsic three-axis coordinate is recovered exactly after encoding it
as `Fin 3` and decoding it with `h3AxisOfFin3`. -/
theorem h3AxisOfFin3_h3ClassicalizationFinOfAxis
    (a : PrimeTensor.Axis Depth.three) :
    h3AxisOfFin3 (h3ClassicalizationFinOfAxis a) = a := by
  exact
    match a with
    | .first => rfl
    | .next .first => rfl
    | .next (.next .first) => rfl

/-- Velocity-component form of the selected mixed derivative theorem.  At every
strict positive interior restart time, differentiating one concrete spatial
partial in time gives the same value as taking that spatial partial of the
actual temporal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
              hν U₀ hA hU₀ r y).component j)
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                hν U₀ hA hU₀ r y).component j)
            t)
        x)
      t := by
  have hScalar :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_hasDerivAt_time
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis a)
      x

  dsimp only at hScalar

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis a
  ] at hScalar

  change
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
              hν U₀ hA hU₀ r
              (h3ClassicalizationFinOfAxis j)))
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r
                  (h3ClassicalizationFinOfAxis j))
                y)
            t)
        x)
      t

  exact hScalar

end

end Euclidean
end Bridge
end PrimeTensor
