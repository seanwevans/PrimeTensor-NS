import PrimeTensor.Fluid.Vorticity.Continuation.H3.Derivative.Order.Two.Selected.Forcing.Second.Coordinate.Fourier.L2.Continuity
import PrimeTensor.Fluid.Vorticity.Continuation.Restart.Mild.Heat.Path

/-!
# Selected forcing Hessian: strong physical L² continuity

The preceding checkpoint proves strong Fourier `L²` continuity of every ordered
second coordinate multiplier of the selected Leray forcing on a positive
terminal slab.

This file transports that path through the standard physical reconstruction

    Fourier L²
      → inverse Plancherel
      → real part
      → `Point3` carrier transport.

All three stages are continuous linear/isometric maps already used by the
order-one closure.  Thus no new analytic estimate is needed here.
-/

namespace PrimeTensor
namespace Bridge
namespace Euclidean

open MeasureTheory FourierTransform
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

noncomputable local instance axisFintypeH3PathOrderTwoSelectedForcingSecondCoordinatePhysicalL2Continuity
    (d : Depth) :
    Fintype (PrimeTensor.Axis d) :=
  Fintype.ofFinite (PrimeTensor.Axis d)

/-- Canonical physical real `L²` reconstruction of one ordered second
coordinate of the selected Leray forcing on a positive terminal slab. -/
noncomputable def h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three)
    (s : Set.Icc (q / 2) q) :
    H3ScalarL2 :=
  h3FromFourierRealL2
    (h3RealPartFourierL2
      ((MeasureTheory.Lp.fourierTransformₗᵢ
          H3FourierPoint3 ℂ).symm
        (h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
          hν U₀ hA hU₀ hq hqR i
          (h3ClassicalizationFinOfAxis a)
          (h3ClassicalizationFinOfAxis b)
          s)))

/-- Every ordered second selected forcing coordinate is strongly continuous in
physical real `L²` on each positive terminal slab. -/
theorem continuous_h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
    {ν A q : ℝ}
    (hν : 0 < ν)
    (U₀ : H3SpectralVelocityState)
    (hA : 0 < A)
    (hU₀ : ‖U₀‖ ≤ A)
    (hq : 0 < q)
    (hqR : q ≤ h3FinHeatLerayRestartRadius ν A)
    (i : Fin 3)
    (a b : PrimeTensor.Axis Depth.three) :
    Continuous
      (h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab
        hν U₀ hA hU₀ hq hqR i a b) := by
  unfold h3SelectedRestartForcingSecondCoordinatePhysicalL2OnSlab

  exact
    continuous_h3FromFourierRealL2.comp
      (continuous_h3RealPartFourierL2.comp
        ((MeasureTheory.Lp.fourierTransformₗᵢ
            H3FourierPoint3 ℂ).symm.continuous.comp
          (continuous_h3SelectedRestartForcingSecondCoordinateFourierL2OnSlab
            hν U₀ hA hU₀ hq hqR i
            (h3ClassicalizationFinOfAxis a)
            (h3ClassicalizationFinOfAxis b))))

end

end Euclidean
end Bridge
end PrimeTensor
