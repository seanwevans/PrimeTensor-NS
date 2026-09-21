import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Third.Partial.Time.Derivative
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Sobolev.Schwartz.Spectral.Classicalization.Selected.Velocity.Real.Second.Mixed.Derivative

/-!
# Classicalization: selected real velocity order-three mixed derivative

The scalar-coordinate order-three theorem now proves

    d/dt (∂ₐ∂ᵦ∂𝑐 uᵢ) = ∂ₐ∂ᵦ∂𝑐 (d/dt uᵢ)

for every strict positive interior restart time.

This file packages that identity directly in the selected real velocity
language.  The only additional step is decoding the three concrete spatial
axes and the velocity-component axis from their `Fin 3` spectral coordinates.

No new estimate, derivative calculation, or mixed-partial argument is used.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators ENNReal NNReal Interval Topology RealInnerProductSpace

noncomputable section

noncomputable local instance axisFintypeH3SelectedVelocityRealThirdMixedDerivative
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

attribute [local instance 1100] NormedSpace.complexToReal

/-- Velocity-component form of the selected order-three mixed derivative
theorem.  At every strict positive interior restart time, differentiating an
ordered concrete third spatial partial in time gives the same value as taking
that ordered third spatial partial of the actual temporal derivative. -/
theorem h3SpectralFinHeatLerayMildSolutionAtRestartRadius_selectedRealVelocity_component_spatial_d_three_hasDerivAt_time
    {ν A t : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (ht : 0 < t)
    (htR : t < h3FinHeatLerayRestartRadius ν A)
    (x : Point3)
    (a b c j : PrimeTensor.Axis Depth.three) :
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (fun y : Point3 =>
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                  hν U₀ hA hU₀ r y).component j)))
          x)
      (spatial3.d
        a
        (spatial3.d
          b
          (spatial3.d
            c
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusSelectedRealVelocity
                    hν U₀ hA hU₀ r y).component j)
                t)))
        x)
      t := by
  have hScalar :=
    h3SpectralFinHeatLerayMildSolutionAtRestartRadius_realC1RepresentativeOnPoint3_spatial_d_three_hasDerivAt_time
      hν U₀ hA hU₀ ht htR
      (h3ClassicalizationFinOfAxis j)
      (h3ClassicalizationFinOfAxis a)
      (h3ClassicalizationFinOfAxis b)
      (h3ClassicalizationFinOfAxis c)
      x

  dsimp only at hScalar

  rw [
    h3AxisOfFin3_h3ClassicalizationFinOfAxis a,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis b,
    h3AxisOfFin3_h3ClassicalizationFinOfAxis c
  ] at hScalar

  change
    HasDerivAt
      (fun r : ℝ =>
        spatial3.d
          a
          (spatial3.d
            b
            (spatial3.d
              c
              (h3SpectralScalarRealC1RepresentativeOnPoint3
                (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                  hν U₀ hA hU₀ r
                  (h3ClassicalizationFinOfAxis j)))))
          x)
      (spatial3.d
        a
        (spatial3.d
          b
          (spatial3.d
            c
            (fun y : Point3 =>
              temporal.d
                (fun r : ℝ =>
                  h3SpectralScalarRealC1RepresentativeOnPoint3
                    (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
                      hν U₀ hA hU₀ r
                      (h3ClassicalizationFinOfAxis j))
                    y)
                t)))
        x)
      t

  exact hScalar

end

end Euclidean
end Bridge
end PrimeTensor
