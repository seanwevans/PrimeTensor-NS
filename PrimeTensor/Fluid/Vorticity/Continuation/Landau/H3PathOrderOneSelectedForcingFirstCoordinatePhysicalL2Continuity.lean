import PrimeTensor.Fluid.Vorticity.Continuation.Landau.H3PathOrderOneSelectedForcingFirstCoordinateFourierL2Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Selected first forcing coordinate: strong physical L² continuity

The preceding checkpoint packages each first coordinate multiplier of the
selected Leray forcing as a strongly continuous Fourier `L²` path on every
positive terminal slab.

This file transports that path through the standard physical reconstruction
pipeline

    Fourier L²
      → inverse Plancherel
      → real part
      → `Point3` carrier transport.

All three stages are already continuous linear/isometric maps in the project,
so no new estimate is needed here.  The resulting physical `H3ScalarL2` path
is strongly continuous on the same slab.

The next checkpoint will identify this canonical physical package a.e. with
the literal first spatial derivative of the selected real Leray forcing.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderOneSelectedForcingFirstCoordinatePhysicalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical real `L²` reconstruction of one first coordinate of the
selected Leray forcing on a positive terminal slab. -/
noncomputable def h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm
        (h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i
          (h3ClassicalizationFinOfAxis a) s)))

/-- Every first selected forcing coordinate is strongly continuous in physical
real `L²` on each positive terminal slab. -/
theorem continuous_h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab
        hν U₀ hA hU₀ hq hqR i a) := by
  unfold h3SelectedRestartForcingFirstCoordinatePhysicalL2OnSlab

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3SelectedRestartForcingFirstCoordinateFourierL2OnSlab
            hν U₀ hA hU₀ hq hqR i
            (h3ClassicalizationFinOfAxis a))))

end

end Euclidean
end Bridge
end PrimeTensor
