import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Canonical.Real.Spatial.Partial.Time.Derivative

/-!
# Classicalization: selected canonical real velocity mixed derivative

The canonical scalar-coordinate chain now proves the actual mixed derivative on
the real `Point3` representative along the modern restart-radius physical
extension:

    d/dt (∂ₐ uᵢ) = ∂ₐ (d/dt uᵢ).

This file packages that scalar theorem into an honest PrimeTensor real velocity
field built directly from the canonical physical extension.

As in the historical selected packaging step, the only representation work is
the exact conversion between an intrinsic `Axis Depth.three` component and its
`Fin 3` spectral coordinate.  No new estimate, derivative calculation,
mixed-partial argument, or PDE identity is introduced.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedCanonicalRealMixedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- The canonical restart-radius spectral path reconstructed as an ordinary
real PrimeTensor velocity field in restart-relative time. -/
noncomputable def h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
    {nu A : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A) :
    SpaceTimeVectorField ℝ ℝ ℝ Depth.three :=
  h3SpectralRealVelocityOfPath
    (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
      hnu U0 hA hU0)

/-- The intrinsic three-axis coordinate is recovered exactly after encoding it
as `Fin 3` and decoding it with `h3AxisOfFin3`.  This is the canonical-package
counterpart of the historical selected helper. -/
theorem h3AxisOfFin3_h3ClassicalizationFinOfAxis_canonical
    (a : PrimeTensor.Axis Depth.three) :
    h3AxisOfFin3 (h3ClassicalizationFinOfAxis a) = a := by
  exact
    match a with
    | .first => rfl
    | .next .first => rfl
    | .next (.next .first) => rfl

/-- Velocity-component form of the canonical selected mixed derivative theorem.
At every strict positive interior restart time, differentiating one concrete
spatial partial in time gives the same value as taking that spatial partial of
the actual temporal derivative. -/
theorem h3SpectralFinHeatLerayRestartRadius_selectedRealVelocity_component_spatial_d_hasDerivAt_time
    {nu A t : ℝ}
    (hnu : 0 < nu)
    (U0 : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU0 : ‖U0‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius nu A)
    (x : Point3)
    (a j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (fun y : Point3 =>
            (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
              hnu U0 hA hU0 r y).component j)
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              (h3SpectralFinHeatLerayRestartRadiusSelectedRealVelocity
                hnu U0 hA hU0 r y).component j)
            t)
        x)
      t := by
  have hScalar :=
    h3SpectralFinHeatLerayRestartRadiusPhysicalExtension_realC1RepresentativeOnPoint3_spatial_d_hasDerivAt_time
      hnu U0 hA hU0 ht htR
      (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis a)
      x

  dsimp only at hScalar

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis_canonical a
  ] at hScalar

  change
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (h3SpectralScalarRealC1RepresentativeOnPoint3
            (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
              hnu U0 hA hU0 r
              (h3ClassicalizationFinOfAxis j)))
          x)
      (spatial3.d
        a
        (fun y : Point3 =>
          temporal.d
            (fun r : ℝ =>
              h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayRestartRadiusPhysicalExtension
                  hnu U0 hA hU0 r
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
