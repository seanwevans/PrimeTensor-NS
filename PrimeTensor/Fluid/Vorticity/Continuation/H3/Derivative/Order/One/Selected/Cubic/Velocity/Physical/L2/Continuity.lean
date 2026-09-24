import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.One.Selected.Cubic.Velocity.Fourier.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Strong physical L² continuity of selected cubic velocity coordinates

The preceding checkpoint packaged every ordered cubic selected velocity
coordinate as a strongly continuous Fourier `L²` path.

This file transports that path through the standard physical reconstruction
pipeline

    Fourier L²
      → inverse Plancherel
      → real part
      → `Point3` carrier transport.

Each stage is already a continuous linear/isometric map in the project.  Thus
no new estimate is required: the `(2π)^3` Fourier-side control transports
immediately to a strongly continuous physical `H3ScalarL2` path.

The next checkpoint can identify this canonical physical `L²` package a.e.
with the literal ordered third spatial derivative of the selected real
velocity and thereby discharge the repeated-index cubic velocity frontier.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedCubicVelocityPhysicalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical real `L²` reconstruction of one ordered cubic
coordinate of a weighted H³ scalar state. -/
noncomputable def h3SpectralScalarRawThirdCoordinatePhysicalL2
    (a b c : PrimeTensor.Axis Depth.three)
    (G : H3SpectralScalarState) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm
        (h3SpectralScalarRawThirdCoordinateFourierL2
          a b c G)))

/-- Physical reconstruction of the cubic coordinate package is continuous as
a map from weighted H³ scalar states to physical real `L²`. -/
theorem continuous_h3SpectralScalarRawThirdCoordinatePhysicalL2
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SpectralScalarRawThirdCoordinatePhysicalL2 a b c) := by
  unfold h3SpectralScalarRawThirdCoordinatePhysicalL2

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3SpectralScalarRawThirdCoordinateFourierL2
            a b c)))

/-- Along the selected restart, every ordered cubic velocity coordinate is
strongly continuous in physical real `L²` on all real source times. -/
theorem continuous_h3SelectedRestartRawThirdCoordinatePhysicalL2
    {ν A : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (i : Fin 3)
    (a b c : PrimeTensor.Axis Depth.three) :
    Continuous
      (fun s : ℝ =>
        h3SpectralScalarRawThirdCoordinatePhysicalL2
          a b c
          (h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
            hν U₀ hA hU₀ s i)) := by
  exact
    (continuous_h3SpectralScalarRawThirdCoordinatePhysicalL2
      a b c).comp
      ((continuous_apply i).comp
        (continuous_h3SpectralFinHeatLerayMildSolutionAtRestartRadiusPhysicalExtension
          hν U₀ hA hU₀))

end

end Euclidean
end Bridge
end PrimeTensor
